/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Reduction.KernelFormalGroupIso
import EllipticCurves.Reduction.PointReduction
import EllipticCurves.FormalGroup.PointsOnIdealTorsion

/-!
# Reduction has no prime-to-`p` torsion in its kernel (issue #346, closes #243)

Let `R` be a **complete** discrete valuation ring (`IsAdicComplete (maximalIdeal R).asIdeal R`) with
fraction field `K = Frac R`, residue field `k` and residue characteristic `p`, and let
`W : WeierstrassCurve K` be an elliptic curve with an integral model.  Combining the group
isomorphism `E₁(K) ≃+ Ê(𝔪)` (`WeierstrassCurve.E₁AddEquiv`, issue #368) with the torsion-freeness of
the formal group `Ê(𝔪)` (`FormalGroup.OnIdeal.eq_zero_of_nsmul_eq_zero`, `PointsOnIdealTorsion`),
this file proves the **analytic heart of Silverman AEC VII.3 Proposition 3.1(a)**: the kernel of
reduction `E₁(K)` has no nontrivial prime-to-`p` torsion.

Concretely, whenever `(m : R)` is a unit — in particular for `m` coprime to the residue
characteristic `p`, since `R` is local with maximal ideal `𝔪` — a point of `E₁(K)` killed by `m` is
`0`:
```
E₁(K)[m] ≃ Ê(𝔪)[m] = 0.
```
Equivalently, a point `P ∈ E(K)` that reduces to the origin (`redPt P = 0`) and has order dividing a
prime-to-`p` integer `m` is itself `O`.

## Main results

* `WeierstrassCurve.E₁_eq_zero_of_isUnit_nsmul` — `E₁(K)` has no nontrivial prime-to-`p` torsion:
  for `IsUnit (m : R)`, `m • P = 0 → P = 0` in `↥(E₁ R W)`.
* `WeierstrassCurve.eq_zero_of_reducesToZero_of_isUnit_nsmul` — the `ReducesToZero` phrasing
  on the affine points `(W⁄K).Point`.
* `WeierstrassCurve.eq_zero_of_redPt_eq_zero_of_isUnit_nsmul` — the reduction-map phrasing: a
  point reducing to the origin with prime-to-`p` order is `O` (needs `HasGoodReduction`).

The full restatement `WeierstrassCurve.reduction_injOn_torsion` (injectivity of the reduction map
on all of `E(K)[m]`) additionally needs the reduction map to be a group homomorphism
(`redPt (P + Q) = redPt P + redPt Q`, issue #360).  ⚠️ **That is now merged**
(`WeierstrassCurve.redPt_add`, `EllipticCurves/Reduction/ReductionHom.lean`), and the restatement
with it: `reduction_injOn_torsion` lives in `EllipticCurves/Reduction/ReductionInjectivity.lean`
and is proved by exactly the argument sketched here — `redPt (P - Q) = 0 ⇒ P - Q ∈ E₁(K)[m] = 0`.
This file supplies its second input.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.3 Prop 3.1(a), VII.2.2.
-/

open IsDiscreteValuationRing

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]
variable (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic]

/-- **The kernel of reduction has no nontrivial prime-to-`p` torsion.**  When `(m : R)` is a unit
(e.g. `m` coprime to the residue characteristic `p`, as `R` is local with maximal ideal `𝔪`), the
only `m`-torsion point of `E₁(K)` is `0`.  This transports the formal-group torsion-freeness
`FormalGroup.OnIdeal.eq_zero_of_nsmul_eq_zero` through the group isomorphism
`E₁AddEquiv : E₁(K) ≃+ Ê(𝔪)` (Silverman AEC VII.3 Prop 3.1(a) / VII.2.2). -/
theorem E₁_eq_zero_of_isUnit_nsmul {m : ℕ} (hm : IsUnit (m : R)) {P : ↥(E₁ R W)}
    (h : m • P = 0) : P = 0 := by
  -- push the hypothesis through the group isomorphism into `Ê(𝔪)`
  have hval : m • E₁AddEquiv R W P = 0 := by rw [← map_nsmul, h, map_zero]
  -- `Ê(𝔪)` is uniquely `m`-divisible for `(m : R)` a unit, so the image is `0`
  have h0 : E₁AddEquiv R W P = 0 := FormalGroup.OnIdeal.eq_zero_of_nsmul_eq_zero hm hval
  -- and the isomorphism is injective
  exact (map_eq_zero_iff (E₁AddEquiv R W) (E₁AddEquiv R W).injective).mp h0

open Classical in
/-- **`ReducesToZero` phrasing.**  A point `P ∈ E(K)` reducing to the origin and killed by an
integer `m` with `(m : R)` a unit (prime-to-`p`) is the identity `O`. -/
theorem eq_zero_of_reducesToZero_of_isUnit_nsmul {m : ℕ} (hm : IsUnit (m : R))
    {P : W.toAffine.Point} (hP : ReducesToZero R W P) (h : m • P = 0) : P = 0 := by
  have hsub : (⟨P, hP⟩ : ↥(E₁ R W)) = 0 := by
    refine E₁_eq_zero_of_isUnit_nsmul R W hm (Subtype.ext ?_)
    rw [AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero]
    exact h
  exact congrArg Subtype.val hsub

open Classical in
/-- **Reduction-map phrasing (Silverman AEC VII.3 Prop 3.1(a)).**  A point `P ∈ E(K)` whose
reduction is the origin (`redPt P = 0`) and whose order divides a prime-to-`p` integer `m`
(with `(m : R)` a unit)
is the identity `O`.  This is the injectivity of reduction *restricted to the kernel* — the
torsion-free heart of the criterion; the full injectivity on `E(K)[m]` additionally needs the
homomorphism property of `redPt` (issue #360). -/
theorem eq_zero_of_redPt_eq_zero_of_isUnit_nsmul [HasGoodReduction R W] {m : ℕ}
    (hm : IsUnit (m : R)) {P : W.toAffine.Point} (hP : redPt R W P = 0) (h : m • P = 0) :
    P = 0 :=
  eq_zero_of_reducesToZero_of_isUnit_nsmul R W hm ((redPt_eq_zero_iff R W P).mp hP) h

end WeierstrassCurve
