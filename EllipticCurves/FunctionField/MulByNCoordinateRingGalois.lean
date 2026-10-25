/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import EllipticCurves.FunctionField.MulByNCoordinateRing
import EllipticCurves.FunctionField.MulByNGalois
import EllipticCurves.FunctionField.PullbackPrincipalityNRationalTorsion
import Mathlib.FieldTheory.Galois.IsGaloisGroup

/-!
# `E[n]` is the Galois group of `[n]∗ : F[W] → F[W][1/ψₙ]`

Let `W` be an elliptic curve over a field `F` and `n` an index with `(2 : F) ≠ 0` and
`(n : F) ≠ 0` (as `NeZero` instances).  `EllipticCurves.FunctionField.MulByNCoordinateRing` makes
`MulByNCover W n = F[W][1/ψₙ]` a finite étale `F[W]`-algebra through the multiplication-by-`n`
map.  This file shows that its automorphism group is `E[n]` acting by translation.

* Translation by `T ∈ E[n]` (`translateAut`) fixes `[n]∗F[W]` (`translateAut_mulByNEndo`), and
  `F[W][1/ψₙ]` is integral over `[n]∗F[W]` and integrally closed, so it preserves
  `F[W][1/ψₙ] ⊆ F(W)` (`exists_algebraMap_eq_of_fix`).  The restrictions form the homomorphism
  `translateAwayHom : TorsionNMul W n →* (AwayPsiN W n ≃ₐ[F] AwayPsiN W n)`, and so a
  `MulSemiringAction (TorsionNMul W n) (MulByNCover W n)` by `F[W]`-algebra automorphisms
  (`smul_algebraMap_mulByNCover`, `algebraMap_smul_mulByNCover`).
* When `#E[n] = n²` for the `F`-rational points (`Nat.card (W.torsion n) = n ^ 2`, all of `E[n]` is
  rational), the fixed field of `E[n]` in `F(W)` is `[n]∗F(W)`
  (`fixedPoints_subfield_eq_mulByNEndoFieldRange_of_card`,
  `EllipticCurves.FunctionField.PullbackPrincipalityNRationalTorsion`), and `F[W]` is integrally
  closed, so
  `isGaloisGroup_mulByNCover_of_card` is Mathlib's `IsGaloisGroup (TorsionNMul W n) F[W] Bₙ` and
  `finrank_mulByNCover_of_card` is `finrank F[W] Bₙ = n²`.
* Over an algebraically closed field the count holds (`card_torsion_eq_sq`), which gives the
  instance `IsGaloisGroup (TorsionNMul W n) W.CoordinateRing (MulByNCover W n)` and
  `finrank_mulByNCover`.

This is the commutative-algebra content of `CurvesJacobian.Cusp.MulNSubgroup` (`sigmaN`,
`autN_bijective`) of `curves-jacobian`, with the scheme layer removed.
-/

open Polynomial Module

namespace WeierstrassCurve.Affine.CoordinateRing

variable {F : Type*} [Field F] (W : Affine F) (n : ℕ) [NeZero (2 : F)] [NeZero (n : F)]
  [W.IsElliptic]

local notation "A" => W.CoordinateRing
local notation "M" => MulByNCover W n
local notation "ι" => algebraMap (AwayPsiN W n) W.FunctionField

instance : IsIntegrallyClosed (AwayPsiN W n) :=
  isIntegrallyClosed_of_isLocalization (R := A) _ (Submonoid.powers (psiN W n))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (psiN_ne_zero W n))

/-! ### Automorphisms of `F(W)` fixing `[n]∗F[W]` preserve `F[W][1/ψₙ]` -/

/-- **A ring endomorphism of `F(W)` fixing `[n]∗F[W]` maps `F[W][1/ψₙ]` into itself**:
`F[W][1/ψₙ]` is integral over `[n]∗F[W]` and integrally closed in `F(W)`. -/
theorem exists_algebraMap_eq_of_fix {σ : W.FunctionField →+* W.FunctionField}
    (hσ : ∀ a : A, σ (ι (mulByNRingHom W n a)) = ι (mulByNRingHom W n a)) (b : AwayPsiN W n) :
    ∃ b' : AwayPsiN W n, ι b' = σ (ι b) := by
  have hb : IsIntegral A (toMulByNCover W n b) := Algebra.IsIntegral.isIntegral _
  have h := IsIntegral.map_of_comp_eq (mulByNRingHom W n)
    (σ.comp ((algebraMap (AwayPsiN W n) W.FunctionField).comp
      ((toMulByNCover W n).symm : MulByNCover W n →+* AwayPsiN W n)))
    (RingHom.ext fun a ↦ (hσ a).symm) hb
  obtain ⟨b', hb'⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact ⟨b', hb'⟩

lemma mem_range_of_fix (σ : W.FunctionField →ₐ[F] W.FunctionField)
    (hσ : ∀ a : A, σ (ι (mulByNRingHom W n a)) = ι (mulByNRingHom W n a)) (b : AwayPsiN W n) :
    σ (ι b) ∈ (IsScalarTower.toAlgHom F (AwayPsiN W n) W.FunctionField).range := by
  obtain ⟨b', h⟩ := exists_algebraMap_eq_of_fix W n (σ := σ.toRingHom) hσ b
  exact ⟨b', h⟩

/-- The restriction to `F[W][1/ψₙ]` of an `F`-algebra endomorphism of `F(W)` fixing `[n]∗F[W]`. -/
noncomputable def restrictAwayAlgHom (σ : W.FunctionField →ₐ[F] W.FunctionField)
    (hσ : ∀ a : A, σ (ι (mulByNRingHom W n a)) = ι (mulByNRingHom W n a)) :
    AwayPsiN W n →ₐ[F] AwayPsiN W n :=
  (AlgEquiv.ofInjective (IsScalarTower.toAlgHom F (AwayPsiN W n) W.FunctionField)
      (algebraMap_awayPsiN_injective W n)).symm.toAlgHom.comp
    ((σ.comp (IsScalarTower.toAlgHom F (AwayPsiN W n) W.FunctionField)).codRestrict
      (IsScalarTower.toAlgHom F (AwayPsiN W n) W.FunctionField).range
      (mem_range_of_fix W n σ hσ))

lemma algebraMap_restrictAwayAlgHom (σ : W.FunctionField →ₐ[F] W.FunctionField)
    (hσ : ∀ a : A, σ (ι (mulByNRingHom W n a)) = ι (mulByNRingHom W n a)) (b : AwayPsiN W n) :
    ι (restrictAwayAlgHom W n σ hσ b) = σ (ι b) :=
  congrArg Subtype.val ((AlgEquiv.ofInjective
    (IsScalarTower.toAlgHom F (AwayPsiN W n) W.FunctionField)
    (algebraMap_awayPsiN_injective W n)).apply_symm_apply
      ((σ.comp (IsScalarTower.toAlgHom F (AwayPsiN W n) W.FunctionField)).codRestrict
        (IsScalarTower.toAlgHom F (AwayPsiN W n) W.FunctionField).range
        (mem_range_of_fix W n σ hσ) b))

/-- The restriction to `F[W][1/ψₙ]` of an `F`-algebra automorphism of `F(W)` fixing `[n]∗F[W]`. -/
noncomputable def restrictAwayAlgEquiv (σ : W.FunctionField ≃ₐ[F] W.FunctionField)
    (hσ : ∀ a : A, σ (ι (mulByNRingHom W n a)) = ι (mulByNRingHom W n a)) :
    AwayPsiN W n ≃ₐ[F] AwayPsiN W n :=
  have hσ' : ∀ a : A, σ.symm (ι (mulByNRingHom W n a)) = ι (mulByNRingHom W n a) := fun a ↦
    σ.symm_apply_eq.2 (hσ a).symm
  AlgEquiv.ofAlgHom (restrictAwayAlgHom W n σ.toAlgHom hσ)
    (restrictAwayAlgHom W n σ.symm.toAlgHom hσ')
    (AlgHom.ext fun b ↦ algebraMap_awayPsiN_injective W n (by
      simp only [AlgHom.comp_apply, AlgHom.coe_id, id_eq, algebraMap_restrictAwayAlgHom]
      exact σ.apply_symm_apply _))
    (AlgHom.ext fun b ↦ algebraMap_awayPsiN_injective W n (by
      simp only [AlgHom.comp_apply, AlgHom.coe_id, id_eq, algebraMap_restrictAwayAlgHom]
      exact σ.symm_apply_apply _))

lemma algebraMap_restrictAwayAlgEquiv (σ : W.FunctionField ≃ₐ[F] W.FunctionField)
    (hσ : ∀ a : A, σ (ι (mulByNRingHom W n a)) = ι (mulByNRingHom W n a)) (b : AwayPsiN W n) :
    ι (restrictAwayAlgEquiv W n σ hσ b) = σ (ι b) :=
  algebraMap_restrictAwayAlgHom W n σ.toAlgHom hσ b

/-! ### The translation action of `E[n]` on `F[W][1/ψₙ]` -/

section Translation


open Classical in
/-- **Translation by an `n`-torsion point fixes `[n]∗F[W]`.** -/
theorem translateAut_algebraMap_mulByNRingHom (T : TorsionNMul W n) (a : A) :
    translateAut (T.toAdd : W.Point) (ι (mulByNRingHom W n a)) = ι (mulByNRingHom W n a) := by
  rw [algebraMap_mulByNRingHom]
  exact translateAut_mulByNEndo n (transcendental_xCoord_nsmul W n) T.toAdd.2 _

open Classical in
/-- **The translations by `E[n]`, restricted to `F[W][1/ψₙ]`**, as a group homomorphism into the
`F`-algebra automorphisms of `F[W][1/ψₙ]`. -/
noncomputable def translateAwayHom : TorsionNMul W n →* (AwayPsiN W n ≃ₐ[F] AwayPsiN W n) where
  toFun T := restrictAwayAlgEquiv W n (translateAut (T.toAdd : W.Point))
    (translateAut_algebraMap_mulByNRingHom W n T)
  map_one' := AlgEquiv.ext fun b ↦ algebraMap_awayPsiN_injective W n (by
    rw [algebraMap_restrictAwayAlgEquiv, AlgEquiv.one_apply, toAdd_one,
      ZeroMemClass.coe_zero, translateAut_zero, AlgEquiv.one_apply])
  map_mul' S T := AlgEquiv.ext fun b ↦ algebraMap_awayPsiN_injective W n (by
    rw [algebraMap_restrictAwayAlgEquiv, AlgEquiv.mul_apply, algebraMap_restrictAwayAlgEquiv,
      algebraMap_restrictAwayAlgEquiv, toAdd_mul, AddSubgroup.coe_add, translateAut_add,
      AlgEquiv.mul_apply])

open Classical in
lemma algebraMap_translateAwayHom (T : TorsionNMul W n) (b : AwayPsiN W n) :
    ι (translateAwayHom W n T b) = translateAut (T.toAdd : W.Point) (ι b) :=
  algebraMap_restrictAwayAlgEquiv W n _ _ b

open Classical in
lemma translateAwayHom_mulByNRingHom (T : TorsionNMul W n) (a : A) :
    translateAwayHom W n T (mulByNRingHom W n a) = mulByNRingHom W n a :=
  algebraMap_awayPsiN_injective W n (by
    rw [algebraMap_translateAwayHom, translateAut_algebraMap_mulByNRingHom])

open Classical in
/-- `E[n]` acts on `MulByNCover W n` by translation. -/
noncomputable instance instMulSemiringActionMulByNCover :
    MulSemiringAction (TorsionNMul W n) M :=
  MulSemiringAction.compHom M
    ((AlgEquiv.autCongr (toMulByNCover W n)).toMonoidHom.comp (translateAwayHom W n))

open Classical in
lemma smul_mulByNCover_def (T : TorsionNMul W n) (b : M) :
    T • b = toMulByNCover W n (translateAwayHom W n T ((toMulByNCover W n).symm b)) := rfl

open Classical in
/-- **The action is translation**: inside `F(W)`, `T • b` is `translateAut T b`. -/
lemma algebraMap_smul_mulByNCover (T : TorsionNMul W n) (b : M) :
    ι ((toMulByNCover W n).symm (T • b)) =
      translateAut (T.toAdd : W.Point) (ι ((toMulByNCover W n).symm b)) := by
  rw [smul_mulByNCover_def, AlgEquiv.symm_apply_apply, algebraMap_translateAwayHom]

open Classical in
/-- **Translations are `F[W]`-algebra automorphisms of `MulByNCover W n`**: they fix `[n]∗F[W]`. -/
lemma smul_algebraMap_mulByNCover (T : TorsionNMul W n) (a : A) :
    T • algebraMap A M a = algebraMap A M a := by
  rw [smul_mulByNCover_def, algebraMap_mulByNCover, AlgEquiv.symm_apply_apply,
    translateAwayHom_mulByNRingHom]

open Classical in
instance : SMulCommClass (TorsionNMul W n) A M where
  smul_comm T a b := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', smul_algebraMap_mulByNCover]

open Classical in
instance : FaithfulSMul (TorsionNMul W n) M where
  eq_of_smul_eq_smul {S T} h := by
    refine translateAutNHom_injective n (AlgEquiv.ext fun f ↦ ?_)
    have hc : (translateAut (S.toAdd : W.Point)).toRingHom.comp ι =
        (translateAut (T.toAdd : W.Point)).toRingHom.comp ι := RingHom.ext fun b ↦ by
      have h' := congrArg (fun z ↦ ι ((toMulByNCover W n).symm z)) (h (toMulByNCover W n b))
      simp only [algebraMap_smul_mulByNCover, AlgEquiv.symm_apply_apply] at h'
      exact h'
    have := IsLocalization.ringHom_ext (nonZeroDivisors (AwayPsiN W n)) hc
    rw [translateAutNHom_apply, translateAutNHom_apply]
    exact RingHom.congr_fun this f

end Translation

/-! ### The Galois group -/

section Galois


open Classical in
/-- **The invariants of `E[n]` in `MulByNCover W n` are `[n]∗F[W]`**, at every `n` with
`(2 : F) ≠ 0`, `(n : F) ≠ 0` and `#E[n] = n²` for the `F`-rational points: an invariant `b`
lies in `[n]∗F(W)` by
`fixedPoints_subfield_eq_mulByNEndoFieldRange_of_card`, its preimage is integral over `F[W]`
because `b` is, and `F[W]` is integrally closed. -/
theorem isInvariant_mulByNCover_of_card (hcard : Nat.card (W.torsion n) = n ^ 2) :
    Algebra.IsInvariant A M (TorsionNMul W n) where
  isInvariant b hb := by
    set hT := transcendental_xCoord_nsmul W n
    let ρ : M →+* W.FunctionField :=
      (algebraMap (AwayPsiN W n) W.FunctionField).comp
        ((toMulByNCover W n).symm : MulByNCover W n →+* AwayPsiN W n)
    have hρ : ρ.comp (algebraMap A M) =
        (mulByNEndo (W := W) n hT).comp (algebraMap A W.FunctionField) :=
      RingHom.ext fun a ↦ algebraMap_mulByNRingHom W n a
    have hfix : ρ b ∈ FixedPoints.subfield (TorsionNMul W n) W.FunctionField := fun T ↦ by
      change translateAut (T.toAdd : W.Point) (ρ b) = ρ b
      have h' := algebraMap_smul_mulByNCover W n T b
      rw [hb T] at h'
      exact h'.symm
    rw [fixedPoints_subfield_eq_mulByNEndoFieldRange_of_card two_ne_zero (NeZero.ne _) hT hcard]
      at hfix
    obtain ⟨u, hu⟩ := hfix
    have hint : IsIntegral A u := by
      obtain ⟨p, hp, hpb⟩ := (Algebra.IsIntegral.isIntegral (R := A) b)
      refine ⟨p, hp, (mulByNEndo (W := W) n hT).injective ?_⟩
      rw [map_zero, hom_eval₂, ← hρ, hu, ← hom_eval₂]
      rw [hpb, map_zero]
    obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨a, (toMulByNCover W n).symm.injective (algebraMap_awayPsiN_injective W n ?_)⟩
    change ρ (algebraMap A M a) = ρ b
    rw [← hu, ← RingHom.comp_apply, hρ, RingHom.comp_apply]

open Classical in
/-- **`E[n]` is the Galois group of `[n]∗ : F[W] → F[W][1/ψₙ]`** in the sense of Mathlib's
`IsGaloisGroup`, at every `n` with `(2 : F) ≠ 0`, `(n : F) ≠ 0` and `#E[n] = n²` for the
`F`-rational points: the translation action is
faithful, commutes with `F[W]`, and has invariants `[n]∗F[W]`. -/
theorem isGaloisGroup_mulByNCover_of_card (hcard : Nat.card (W.torsion n) = n ^ 2) :
    IsGaloisGroup (TorsionNMul W n) A M where
  faithful := inferInstance
  commutes := inferInstance
  isInvariant := isInvariant_mulByNCover_of_card W n hcard

open Classical in
/-- **`finrank F[W] F[W][1/ψₙ] = n²`** via `[n]∗`, at every `n` with `(2 : F) ≠ 0`, `(n : F) ≠ 0`
and `#E[n] = n²` for the `F`-rational points. -/
theorem finrank_mulByNCover_of_card (hcard : Nat.card (W.torsion n) = n ^ 2) :
    finrank A M = n ^ 2 := by
  haveI := isGaloisGroup_mulByNCover_of_card W n hcard
  haveI : FaithfulSMul A M :=
    (faithfulSMul_iff_algebraMap_injective A M).2 (algebraMap_mulByNCover_injective W n)
  have hcard' : Nat.card (TorsionNMul W n) = n ^ 2 :=
    (Nat.card_congr Multiplicative.toAdd).trans hcard
  haveI : Finite (TorsionNMul W n) := Nat.finite_of_card_ne_zero (by
    rw [hcard']; exact pow_ne_zero 2 (ne_zero_of_neZero_cast (F := F) n))
  rw [← IsGaloisGroup.card_eq_finrank' (TorsionNMul W n) A M, hcard']

section IsAlgClosed

variable [IsAlgClosed F]

open Classical in
/-- **`E[n]` is the Galois group of `[n]∗ : F[W] → F[W][1/ψₙ]`** over an algebraically closed
field, at every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`. -/
instance isGaloisGroup_mulByNCover : IsGaloisGroup (TorsionNMul W n) A M :=
  isGaloisGroup_mulByNCover_of_card W n (card_torsion_eq_sq two_ne_zero (NeZero.ne _))

open Classical in
/-- **`finrank F[W] F[W][1/ψₙ] = n²`** via `[n]∗`, over an algebraically closed field, at every `n`
with `(2 : F) ≠ 0` and `(n : F) ≠ 0`. -/
theorem finrank_mulByNCover : finrank A M = n ^ 2 :=
  finrank_mulByNCover_of_card W n (card_torsion_eq_sq two_ne_zero (NeZero.ne _))

end IsAlgClosed

end Galois

end WeierstrassCurve.Affine.CoordinateRing
