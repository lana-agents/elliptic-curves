/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Reduction.InverseAdditivity
import EllipticCurves.Reduction.KernelFormalGroup

/-!
# The formal-inverse compatibility of the local parameter (issue #367, partial)

Let `R` be a complete discrete valuation ring with fraction field `K = Frac R` and
`W : WeierstrassCurve K` an elliptic curve with an integral model.  Working in the genuine
formal-group carrier `Ê(𝔪) = FormalGroup.OnIdeal (integralModel R W).formalGroup 𝔪`
(`Reduction/KernelFormalGroup.lean`), this file packages the **inverse case** of the additivity
crux `z(P + Q) = z(P) ⊕ z(Q)` (issue #367) at the group level:

```
zParamHatEquiv (-P) = - zParamHatEquiv P     in Ê(𝔪),
```

whenever `P ≠ -P` (equivalently `P` is not `2`-torsion).  This is Silverman's `z ∘ [-1] = i(z)`
(AEC IV.1): the local parameter intertwines curve negation with the formal inverse.

The analytic content is the merged **vertical additivity**
`adicEvalMv 𝔪 ![z(P), z(-P)] formalGroupZW = 0` (`Reduction/InverseAdditivity.lean`, PR #102),
proved from the fact that two points sharing an `x`-coordinate span a chord through the origin, so
their formal-group sum is `0`.  Since `Ê(𝔪)` is a group, `z(P) ⊕ z(-P) = 0` upgrades to
`z(-P) = ⊖ z(P)` by `eq_neg_of_add_eq_zero_right`.

The hypothesis `P ≠ -P` rules out the identity `O` (there `-P = P`) and the `2`-torsion points;
for those the statement `z(-P) = ⊖ z(P)` still holds but reduces, respectively, to
`0 = ⊖ 0` and to `z(P)` being formal-`2`-torsion, which needs the doubling additivity rather than
this vertical slice.

## Main results

* `WeierstrassCurve.zParamHatEquiv_add_neg_eq_zero` — the group-level vertical additivity
  `zParamHatEquiv P + zParamHatEquiv (-P) = 0` for `P ≠ -P`.
* `WeierstrassCurve.zParamHatEquiv_neg` — the formal-inverse compatibility
  `zParamHatEquiv (-P) = - zParamHatEquiv P` for `P ≠ -P`.

## References

Silverman, *The Arithmetic of Elliptic Curves*, IV.1, VII.2 Prop 2.2.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]
variable (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic]

/-- The subtype element `-P ∈ E₁(K)` obtained from `P ∈ E₁(K)` via `reducesToZero_neg`
(the reduction kernel is closed under negation). -/
noncomputable def negReduces (P : {P : W.toAffine.Point // ReducesToZero R W P}) :
    {P : W.toAffine.Point // ReducesToZero R W P} :=
  ⟨-P.1, (reducesToZero_neg R W P.1).mpr P.2⟩

omit [IsAdicComplete (maximalIdeal R).asIdeal R] [W.IsElliptic] in
@[simp] theorem negReduces_val (P : {P : W.toAffine.Point // ReducesToZero R W P}) :
    (negReduces R W P).1 = -P.1 := rfl

/-- **The local parameters of `P` and `-P` are distinct when `P ≠ -P`.**  `zParam` is injective
(`zParam_injective`), so equal local parameters would force `P = -P`. -/
theorem localParamR_neg_ne (P : {P : W.toAffine.Point // ReducesToZero R W P})
    (hne : P.1 ≠ -P.1) :
    localParamR R W P.1 ≠ localParamR R W (-P.1) := by
  intro heq
  apply hne
  have hsub : zParam R W P = zParam R W (negReduces R W P) := Subtype.ext heq
  exact congrArg Subtype.val (zParam_injective R W hsub)

/-- **Group-level vertical additivity.**  For `P ∈ E₁(K)` with `P ≠ -P`, the formal-group sum of
the local parameters of `P` and `-P` vanishes in `Ê(𝔪)`.  This is the group packaging of the
merged `adicEvalMv_formalGroupZW_eq_zero_of_X_eq` (PR #102): two points with a common
`x`-coordinate span a chord through the origin, so `z(P) ⊕ z(-P) = 0`. -/
theorem zParamHatEquiv_add_neg_eq_zero
    (P : {P : W.toAffine.Point // ReducesToZero R W P}) (hne : P.1 ≠ -P.1) :
    zParamHatEquiv R W P + zParamHatEquiv R W (negReduces R W P) = 0 := by
  obtain ⟨P, hP⟩ := P
  cases P with
  | zero =>
    refine absurd ?_ hne
    change (0 : W.toAffine.Point) = -(0 : W.toAffine.Point)
    simp
  | some x y h =>
    apply FormalGroup.OnIdeal.ext
    rw [zParamHatEquiv_add_val, FormalGroup.OnIdeal.zero_val]
    have hx : 1 < valuation K (maximalIdeal R) x := hP
    have hz12 : localParamR R W (.some x y h) ≠ localParamR R W (-(.some x y h)) :=
      localParamR_neg_ne R W ⟨.some x y h, hP⟩ hne
    exact adicEvalMv_formalGroupZW_eq_zero_of_X_eq R W hx
      (FormalGroup.OnIdeal.memFin2 (maximalIdeal R).asIdeal
        (zParamHatEquiv R W ⟨.some x y h, hP⟩).property
        (zParamHatEquiv R W (negReduces R W ⟨.some x y h, hP⟩)).property) hz12

/-- **The formal-inverse compatibility `z ∘ [-1] = i(z)` (Silverman AEC IV.1).**  For `P ∈ E₁(K)`
with `P ≠ -P`, the local parameter of `-P` is the formal-group inverse of the local parameter of
`P`:
`zParamHatEquiv (-P) = - zParamHatEquiv P` in `Ê(𝔪)`.  This is the group-level packaging of the
inverse case of the additivity crux (issue #367), consuming the vertical additivity of PR #102. -/
theorem zParamHatEquiv_neg
    (P : {P : W.toAffine.Point // ReducesToZero R W P}) (hne : P.1 ≠ -P.1) :
    zParamHatEquiv R W (negReduces R W P) = - zParamHatEquiv R W P :=
  eq_neg_of_add_eq_zero_right (zParamHatEquiv_add_neg_eq_zero R W P hne)

end WeierstrassCurve
