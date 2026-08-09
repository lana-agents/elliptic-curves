/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Reduction.KernelNegationUncond
import EllipticCurves.Reduction.AdditivityUncond
import EllipticCurves.Reduction.KernelAddClosure

/-!
# The group isomorphism `E₁(K) ≃+ Ê(𝔪)` (issues #367, #368)

Let `R` be a complete discrete valuation ring with fraction field `K = Frac R` and
`W : WeierstrassCurve K` an elliptic curve with an integral model.  This file assembles the final
deliverable of the reduction-kernel formal-group identification: the **isomorphism of abelian
groups**
```
E₁(K) ≃+ Ê(𝔪),   Ê(𝔪) = FormalGroup.OnIdeal (integralModel R W).formalGroup 𝔪.
```

It upgrades the merged set bijection `zParamHatEquiv : E₁(K) ≃ Ê(𝔪)`
(`Reduction/KernelFormalGroup.lean`) to an `AddEquiv`, supplying `map_add'` from the four-case
additivity identity `z(P + Q) = z(P) ⊕ z(Q)` (Silverman AEC VII.2 Prop 2.2), which mirrors the
add-closure case tree `reducesToZero_add` (`Reduction/KernelAddClosure.lean`):

* `P = O` / `Q = O` — trivial via `zParamHatEquiv_zero`;
* **vertical** (`Q = -P`) — the formal-inverse compatibility `z(-P) = -z(P)`, now *unconditional*
  (`zParamHatEquiv_neg_uncond`, issue #377, which covers the `2`-torsion corner);
* **doubling** (`x₁ = x₂`, `2P ≠ O`) — `localParam_add_of_X_eq_uncond` (issue #367);
* **secant** (`x₁ ≠ x₂`) — `localParam_add_of_X_ne_uncond` (issue #367).

## Main results

* `WeierstrassCurve.zParamHatEquiv_map_add` — the additivity identity for all `P, Q ∈ E₁(K)`.
* `WeierstrassCurve.E₁AddEquiv` — the group isomorphism `E₁(K) ≃+ Ê(𝔪)`.

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
/-- **The additivity identity `z(P + Q) = z(P) ⊕ z(Q)` on the reduction kernel (#367, #368).**
For all `P, Q ∈ E₁(K)`, the formal-group image `zParamHatEquiv` of the affine sum equals the
`Ê(𝔪)`-sum of the images.  The four cases mirror the add-closure `reducesToZero_add`. -/
theorem zParamHatEquiv_map_add
    (P Q : {P : W.toAffine.Point // ReducesToZero R W P}) :
    zParamHatEquiv R W ⟨P.1 + Q.1, reducesToZero_add R W P.2 Q.2⟩
      = zParamHatEquiv R W P + zParamHatEquiv R W Q := by
  obtain ⟨P, hP⟩ := P
  obtain ⟨Q, hQ⟩ := Q
  change zParamHatEquiv R W ⟨P + Q, reducesToZero_add R W hP hQ⟩
    = zParamHatEquiv R W ⟨P, hP⟩ + zParamHatEquiv R W ⟨Q, hQ⟩
  cases P with
  | zero =>
    -- `O + Q = Q`, and `z(O) = 0`
    have h0 : zParamHatEquiv R W ⟨Affine.Point.zero, hP⟩ = 0 := zParamHatEquiv_zero R W
    have hsub : (⟨Affine.Point.zero + Q, reducesToZero_add R W hP hQ⟩ :
        {P : W.toAffine.Point // ReducesToZero R W P}) = ⟨Q, hQ⟩ := Subtype.ext (zero_add Q)
    rw [hsub, h0, zero_add]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      -- `P + O = P`, and `z(O) = 0`
      have h0 : zParamHatEquiv R W ⟨Affine.Point.zero, hQ⟩ = 0 := zParamHatEquiv_zero R W
      have hsub : (⟨Affine.Point.some x₁ y₁ h₁ + Affine.Point.zero, reducesToZero_add R W hP hQ⟩ :
          {P : W.toAffine.Point // ReducesToZero R W P})
            = ⟨Affine.Point.some x₁ y₁ h₁, hP⟩ := Subtype.ext (add_zero _)
      rw [hsub, h0, add_zero]
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
      · -- vertical: `Q = -P`, so `P + Q = O` and `z(P) ⊕ z(Q) = z(P) ⊕ (-z(P)) = 0`
        have hsum0 : (Affine.Point.some x₁ y₁ h₁ + Affine.Point.some x₂ y₂ h₂ :
            W.toAffine.Point) = 0 := Affine.Point.add_of_Y_eq hxy.1 hxy.2
        have hlhs : zParamHatEquiv R W
            ⟨Affine.Point.some x₁ y₁ h₁ + Affine.Point.some x₂ y₂ h₂,
              reducesToZero_add R W hP hQ⟩ = 0 := by
          rw [show (⟨Affine.Point.some x₁ y₁ h₁ + Affine.Point.some x₂ y₂ h₂,
              reducesToZero_add R W hP hQ⟩ : {P : W.toAffine.Point // ReducesToZero R W P})
                = ⟨0, reducesToZero_zero R W⟩ from Subtype.ext hsum0]
          exact zParamHatEquiv_zero R W
        have hQP : (⟨Affine.Point.some x₂ y₂ h₂, hQ⟩ :
            {P : W.toAffine.Point // ReducesToZero R W P})
              = negReduces R W ⟨Affine.Point.some x₁ y₁ h₁, hP⟩ := by
          apply Subtype.ext
          rw [negReduces_val, Affine.Point.neg_some, Affine.Point.some.injEq]
          refine ⟨hxy.1.symm, ?_⟩
          rw [hxy.1, hxy.2, Affine.negY_negY]
        rw [hlhs, hQP, zParamHatEquiv_neg_uncond, add_neg_cancel]
      · by_cases hx : x₁ = x₂
        · -- doubling: `x₁ = x₂`, not vertical ⇒ `y₁ = y₂` ⇒ `Q = P`
          have hyne : y₁ ≠ W.toAffine.negY x₂ y₂ := fun hy => hxy ⟨hx, hy⟩
          have hyeq : y₁ = y₂ := Affine.Y_eq_of_Y_ne h₁.1 h₂.1 hx hyne
          -- unify `Q` with `P`: `x₂ = x₁`, `y₂ = y₁`, and `h₂ = h₁` by proof irrelevance
          subst hx
          subst hyeq
          obtain rfl : h₁ = h₂ := Subsingleton.elim _ _
          have hY1 : y₁ ≠ W.toAffine.negY x₁ y₁ := hyne
          apply FormalGroup.OnIdeal.ext
          rw [zParamHatEquiv_add_val, zParamHatEquiv_val]
          apply IsFractionRing.injective R K
          rw [algebraMap_localParamR]
          exact localParam_add_of_X_eq_uncond R W hP (reducesToZero_add R W hP hQ) hY1
        · -- secant: `x₁ ≠ x₂`
          have ha : ∀ s : Fin 2,
              ![localParamR R W (.some x₁ y₁ h₁), localParamR R W (.some x₂ y₂ h₂)] s
                ∈ (maximalIdeal R).asIdeal := by
            intro s
            fin_cases s
            · exact localParamR_mem R W hP
            · exact localParamR_mem R W hQ
          apply FormalGroup.OnIdeal.ext
          rw [zParamHatEquiv_add_val, zParamHatEquiv_val]
          apply IsFractionRing.injective R K
          rw [algebraMap_localParamR]
          exact localParam_add_of_X_ne_uncond R W hP hQ hx (reducesToZero_add R W hP hQ) ha

open Classical in
/-- **The group isomorphism `E₁(K) ≃+ Ê(𝔪)` (issues #367, #368).**  Upgrade of the set bijection
`zParamHatEquiv` to an isomorphism of abelian groups, with `map_add` supplied by
`zParamHatEquiv_map_add`.  This is Silverman AEC VII.2 Prop 2.2: the kernel of reduction is
isomorphic (as an abelian group) to the formal group evaluated on the maximal ideal. -/
noncomputable def E₁AddEquiv : ↥(E₁ R W) ≃+ formalGroupOnMaximal R W :=
  AddEquiv.mk' (zParamHatEquiv R W) (fun P Q => zParamHatEquiv_map_add R W P Q)

@[simp] theorem E₁AddEquiv_apply (P : ↥(E₁ R W)) :
    E₁AddEquiv R W P = zParamHatEquiv R W P := rfl

end WeierstrassCurve
