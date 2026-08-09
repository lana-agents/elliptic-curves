/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Reduction.IntegralReductionAdd
import EllipticCurves.Reduction.KernelIntegralReduction
import EllipticCurves.Reduction.KernelVerticalReduction

/-!
# Reduction on points is a group homomorphism (issue #383, closing #360)

Let `R` be a complete discrete valuation ring with fraction field `K = Frac R` and residue field
`k`, and let `W : WeierstrassCurve K` be elliptic with good reduction.  This file performs the final
assembly of the point-reduction homomorphism: it glues the case rungs into the unconditional
additivity `map_add`, packages the set-level reduction map `redPt` as an `AddMonoidHom`
`redHom : (W⁄K).Point →+ (reduction R W).Point`, and identifies the reduction kernel `E₁(K)` (the
`AddSubgroup` from `KernelAddClosure`) with `redHom.ker`.

## The case dispatch

For `P = (x₁, y₁)`, `Q = (x₂, y₂)` the additivity `redPt (P + Q) = redPt P + redPt Q` is proved by
splitting on whether each summand is integral (`v xᵢ ≤ 1`) or a pole (`1 < v xᵢ`), routing to the
rung lemmas already on `main`:

* both integral → `redPt_add_of_both_integral` (#383/#120, the good-reduction locus);
* pole × integral / integral × pole → `redPt_add_of_mem_E₁_left` / `_right` (#384, the
  kernel-acts-trivially case), with the pole summand's `redPt` collapsing to `0` via
  `redPt_some_of_one_lt`;
* both poles → `redPt_add_of_reducesToZero` (#382, kernel × kernel closure);
* `P = O` or `Q = O` → trivial (`redPt_zero`).

## Main results

* `WeierstrassCurve.redPt_add` — `redPt (P + Q) = redPt P + redPt Q` for all `P, Q`.
* `WeierstrassCurve.redHom` — the reduction homomorphism `(W⁄K).Point →+ (reduction R W).Point`.
* `WeierstrassCurve.E₁_eq_ker` — `E₁ R W = (redHom R W).ker`.

## References

Silverman, *The Arithmetic of Elliptic Curves*, VII.2 Prop 2.1, 2.2.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum WithZero Multiplicative

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]
variable (W : WeierstrassCurve K) [HasGoodReduction R W] [W.IsElliptic]

omit [IsAdicComplete (maximalIdeal R).asIdeal R] [W.IsElliptic] in
/-- Good reduction makes the reduced curve elliptic; registered as a file-local instance so the
`AddCommGroup` on `(reduction R W).Point` is available for the bundled homomorphism `redHom`. -/
private theorem reduction_isElliptic : (reduction R W).IsElliptic :=
  (hasGoodReduction_iff_isElliptic_reduction R).mp inferInstance

attribute [local instance] reduction_isElliptic

/-! ### Unconditional additivity of `redPt` -/

open Classical in
/-- **The reduction map on points is additive.**  `redPt (P + Q) = redPt P + redPt Q` for all
`P, Q : (W⁄K).Point`.  The proof dispatches on whether each summand is integral (`v x ≤ 1`) or a
pole (`1 < v x`) and routes to the corresponding rung lemma. -/
theorem redPt_add (P Q : W.toAffine.Point) :
    redPt R W (P + Q) = redPt R W P + redPt R W Q := by
  have hz : redPt R W (0 : W.toAffine.Point) = 0 := redPt_zero R W
  cases P with
  | zero =>
    change redPt R W (0 + Q) = redPt R W 0 + redPt R W Q
    rw [zero_add, hz, zero_add]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      change redPt R W (Affine.Point.some x₁ y₁ h₁ + 0)
        = redPt R W (Affine.Point.some x₁ y₁ h₁) + redPt R W 0
      rw [add_zero, hz, add_zero]
    | some x₂ y₂ h₂ =>
      by_cases hx₁ : valuation K (maximalIdeal R) x₁ ≤ 1
      · by_cases hx₂ : valuation K (maximalIdeal R) x₂ ≤ 1
        · -- both integral
          exact redPt_add_of_both_integral R W hx₁ hx₂
        · -- `P` integral, `Q` a pole: `redPt Q = 0`, and adding `Q` fixes the reduction of `P`
          obtain ⟨x₀₁, hx₀₁⟩ := exists_lift_of_le_one hx₁
          obtain ⟨y₀₁, hy₀₁⟩ := exists_lift_of_le_one (valuation_y_le_one_of_le_one R W h₁.1 hx₁)
          rw [redPt_add_of_mem_E₁_right R W hx₀₁ hy₀₁ hx₁ (not_le.mp hx₂),
            redPt_some_of_one_lt R W (not_le.mp hx₂), add_zero]
      · by_cases hx₂ : valuation K (maximalIdeal R) x₂ ≤ 1
        · -- `P` a pole, `Q` integral: `redPt P = 0`, and adding `P` fixes the reduction of `Q`
          obtain ⟨x₀₂, hx₀₂⟩ := exists_lift_of_le_one hx₂
          obtain ⟨y₀₂, hy₀₂⟩ := exists_lift_of_le_one (valuation_y_le_one_of_le_one R W h₂.1 hx₂)
          rw [redPt_add_of_mem_E₁_left R W hx₀₂ hy₀₂ hx₂ (not_le.mp hx₁),
            redPt_some_of_one_lt R W (not_le.mp hx₁), zero_add]
        · -- both poles (kernel × kernel)
          exact redPt_add_of_reducesToZero R W
            ((reducesToZero_some_iff R W).mpr (not_le.mp hx₁))
            ((reducesToZero_some_iff R W).mpr (not_le.mp hx₂))

/-! ### The reduction homomorphism and its kernel -/

open Classical in
/-- **The reduction homomorphism** `redHom : (W⁄K).Point →+ (reduction R W).Point`, packaging the
set-level `redPt` via `AddMonoidHom.mk'` from its additivity `redPt_add` (`redPt_zero` supplies
`map_zero`). -/
noncomputable def redHom : W.toAffine.Point →+ (reduction R W).toAffine.Point :=
  AddMonoidHom.mk' (redPt R W) (redPt_add R W)

open Classical in
@[simp] theorem redHom_apply (P : W.toAffine.Point) : redHom R W P = redPt R W P := rfl

open Classical in
/-- **The reduction kernel is the kernel of the reduction homomorphism.**  The `AddSubgroup`
`E₁ R W = {P | ReducesToZero R W P}` (from `KernelAddClosure`) coincides with `(redHom R W).ker`,
via `redPt_eq_zero_iff`. -/
theorem E₁_eq_ker : E₁ R W = (redHom R W).ker := by
  ext P
  rw [mem_E₁, AddMonoidHom.mem_ker, redHom_apply, redPt_eq_zero_iff]

end WeierstrassCurve
