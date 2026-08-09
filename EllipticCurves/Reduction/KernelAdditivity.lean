/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Reduction.AdditivityUncond
import EllipticCurves.Reduction.KernelAddClosure
import EllipticCurves.Reduction.KernelFormalGroup
import EllipticCurves.Reduction.KernelNegationUncond

/-!
# The local-parameter additivity `zParamHatEquiv (P + Q) = zParamHatEquiv P ⊕ Q` (issue #367)

Let `R` be a **complete** discrete valuation ring (`IsAdicComplete (maximalIdeal R).asIdeal R`) with
fraction field `K = Frac R`, and let `W : WeierstrassCurve K` be an elliptic curve (`W.IsElliptic`)
with an integral model (`IsIntegral R W`).  Working in the genuine formal-group carrier
`Ê(𝔪) = FormalGroup.OnIdeal (integralModel R W).formalGroup 𝔪` (`Reduction/KernelFormalGroup.lean`),
this file assembles the **group-law compatibility** of the local parameter — the heart of #361 /
Silverman AEC VII.2 Prop 2.2:

```
zParamHatEquiv (P + Q) = zParamHatEquiv P + zParamHatEquiv Q     in Ê(𝔪),   for all P, Q ∈ E₁(K).
```

The proof mirrors the case split of `reducesToZero_add` (`Reduction/KernelAddClosure.lean`),
feeding each case to a merged unconditional brick:

* `P = O` / `Q = O` — trivial via `zParamHatEquiv_zero` + `zero_add` / `add_zero`;
* vertical (`Q = -P`, i.e. `x₁ = x₂` and `y₁ = negY x₂ y₂`) — here `P + Q = O`, so the left side is
  `0`, and the right side vanishes by the **unconditional** inverse compatibility
  `zParamHatEquiv_neg_uncond` (`Reduction/KernelNegationUncond.lean`, issue #377): it handles the
  `2`-torsion corner `P = -P` that the earlier `zParamHatEquiv_add_neg_eq_zero` (which needs
  `P ≠ -P`) cannot;
* doubling (`x₁ = x₂`, `2P ≠ O`) — `localParam_add_of_X_eq_uncond` (in `AdditivityUncond.lean`);
* secant (`x₁ ≠ x₂`) — `localParam_add_of_X_ne_uncond` (in `AdditivityUncond.lean`).

This is the additivity identity #368's group-isomorphism upgrade `E₁(K) ≃+ Ê(𝔪)` consumes as its
`map_add'`.  The reduction kernel is already an `AddSubgroup` (`WeierstrassCurve.E₁`,
`Reduction/KernelAddClosure.lean`).

## Main result

* `WeierstrassCurve.zParamHatEquiv_map_add` — the additivity identity above.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, VII.2 Prop 2.2.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]
variable (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic]

open Classical in
/-- **The additivity identity `z(P + Q) = z(P) ⊕ z(Q)` (Silverman AEC VII.2 Prop 2.2).**  For all
`P, Q ∈ E₁(K)` (points reducing to the origin), the local parameter of the curve sum is the
formal-group sum of the individual local parameters, in the genuine carrier `Ê(𝔪)`.  This is the
`map_add'` the group isomorphism `E₁(K) ≃+ Ê(𝔪)` (issue #368) is built from.

The case split mirrors `reducesToZero_add`: the identity cases are trivial; the vertical case
`Q = -P` uses the unconditional `zParamHatEquiv_neg_uncond` (issue #377, covering the `2`-torsion
corner `P = -P`); the doubling and secant cases use the unconditional coordinate-additivity bricks
`localParam_add_of_X_eq_uncond` / `localParam_add_of_X_ne_uncond`. -/
theorem zParamHatEquiv_map_add
    (P Q : {P : W.toAffine.Point // ReducesToZero R W P}) :
    zParamHatEquiv R W ⟨P.1 + Q.1, reducesToZero_add R W P.2 Q.2⟩
      = zParamHatEquiv R W P + zParamHatEquiv R W Q := by
  obtain ⟨Pt, hP⟩ := P
  obtain ⟨Qt, hQ⟩ := Q
  change zParamHatEquiv R W ⟨Pt + Qt, reducesToZero_add R W hP hQ⟩
      = zParamHatEquiv R W ⟨Pt, hP⟩ + zParamHatEquiv R W ⟨Qt, hQ⟩
  cases Pt with
  | zero =>
    -- `O + Q = Q` and `z(O) = 0`
    have hsum : (⟨Affine.Point.zero + Qt, reducesToZero_add R W hP hQ⟩
        : {P : W.toAffine.Point // ReducesToZero R W P}) = ⟨Qt, hQ⟩ :=
      Subtype.ext (zero_add Qt)
    have h0 : zParamHatEquiv R W ⟨Affine.Point.zero, hP⟩ = 0 := zParamHatEquiv_zero R W
    rw [hsum, h0, zero_add]
  | some x₁ y₁ h₁ =>
    cases Qt with
    | zero =>
      -- `P + O = P` and `z(O) = 0`
      have hsum : (⟨Affine.Point.some x₁ y₁ h₁ + Affine.Point.zero,
          reducesToZero_add R W hP hQ⟩ : {P : W.toAffine.Point // ReducesToZero R W P})
          = ⟨.some x₁ y₁ h₁, hP⟩ :=
        Subtype.ext (add_zero _)
      have h0 : zParamHatEquiv R W ⟨Affine.Point.zero, hQ⟩ = 0 := zParamHatEquiv_zero R W
      rw [hsum, h0, add_zero]
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
      · -- vertical: `Q = -P`, so `P + Q = O` and `z(P) ⊕ z(Q) = z(P) ⊕ (-z(P)) = 0`
        have hy2 : W.toAffine.negY x₁ y₁ = y₂ := by
          rw [hxy.2, ← hxy.1, Affine.negY_negY]
        have hQeq : (⟨.some x₂ y₂ h₂, hQ⟩ : {P : W.toAffine.Point // ReducesToZero R W P})
            = negReduces R W ⟨.some x₁ y₁ h₁, hP⟩ := by
          apply Subtype.ext
          rw [negReduces_val, Affine.Point.neg_some, Affine.Point.some.injEq]
          exact ⟨hxy.1.symm, hy2.symm⟩
        have hsum : (⟨Affine.Point.some x₁ y₁ h₁ + .some x₂ y₂ h₂, reducesToZero_add R W hP hQ⟩
            : {P : W.toAffine.Point // ReducesToZero R W P})
            = ⟨Affine.Point.zero, reducesToZero_zero R W⟩ :=
          Subtype.ext (Affine.Point.add_of_Y_eq hxy.1 hxy.2)
        rw [hsum, zParamHatEquiv_zero, hQeq, zParamHatEquiv_neg_uncond, add_neg_cancel]
      · by_cases hx : x₁ = x₂
        · -- doubling: `x₁ = x₂` and not vertical ⇒ `y₁ = y₂` ⇒ `Q = P`, `2P ≠ O`
          have hyne : y₁ ≠ W.toAffine.negY x₂ y₂ := fun hy => hxy ⟨hx, hy⟩
          have hyeq : y₁ = y₂ := Affine.Y_eq_of_Y_ne h₁.1 h₂.1 hx hyne
          have hneg : W.toAffine.negY x₁ y₁ = W.toAffine.negY x₂ y₂ := by rw [hx, hyeq]
          have hY1 : y₁ ≠ W.toAffine.negY x₁ y₁ := by rw [hneg]; exact hyne
          have hQPt : (Affine.Point.some x₂ y₂ h₂ : W.toAffine.Point) = .some x₁ y₁ h₁ := by
            rw [Affine.Point.some.injEq]; exact ⟨hx.symm, hyeq.symm⟩
          have hQP : (⟨.some x₂ y₂ h₂, hQ⟩ : {P : W.toAffine.Point // ReducesToZero R W P})
              = ⟨.some x₁ y₁ h₁, hP⟩ := Subtype.ext hQPt
          have hLHS : (⟨Affine.Point.some x₁ y₁ h₁ + .some x₂ y₂ h₂, reducesToZero_add R W hP hQ⟩
              : {P : W.toAffine.Point // ReducesToZero R W P})
              = ⟨.some x₁ y₁ h₁ + .some x₁ y₁ h₁, reducesToZero_add R W hP hP⟩ :=
            Subtype.ext (congrArg (Affine.Point.some x₁ y₁ h₁ + ·) hQPt)
          rw [hLHS, hQP]
          apply FormalGroup.OnIdeal.ext
          rw [zParamHatEquiv_add_val, zParamHatEquiv_val]
          apply IsFractionRing.injective R K
          rw [algebraMap_localParamR]
          exact localParam_add_of_X_eq_uncond R W hP (reducesToZero_add R W hP hP) hY1
        · -- secant: `x₁ ≠ x₂`
          apply FormalGroup.OnIdeal.ext
          rw [zParamHatEquiv_add_val, zParamHatEquiv_val]
          apply IsFractionRing.injective R K
          rw [algebraMap_localParamR]
          exact localParam_add_of_X_ne_uncond R W hP hQ hx (reducesToZero_add R W hP hQ)
            (FormalGroup.OnIdeal.memFin2 (maximalIdeal R).asIdeal
              (zParamHatEquiv R W ⟨.some x₁ y₁ h₁, hP⟩).property
              (zParamHatEquiv R W ⟨.some x₂ y₂ h₂, hQ⟩).property)

end WeierstrassCurve
