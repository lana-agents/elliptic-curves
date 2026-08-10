/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByThreeEndomorphism
import EllipticCurves.FunctionField.MulByTwoModuleFinite

/-!
# Finiteness of the multiplication-by-`3` function-field extension `F(W) / [3]∗F(W)`

Let `W` be a Weierstrass curve over a field `F` of characteristic `≠ 2, 3`, with function field
`F(W) = Frac F[W]`. The multiplication-by-`3` endomorphism
`mulByThreeEndo h2 h3 : F(W) →+* F(W)` (`EllipticCurves/FunctionField/MulByThreeEndomorphism.lean`)
is an injective field homomorphism; its image `[3]∗F(W)` is a subfield of `F(W)`, and the extension
`F(W) / [3]∗F(W)` is the degree-`9` extension underlying the fact that `[3] : E → E` is a finite
morphism of degree `9 = 3²`. This file supplies the **finiteness datum** for the
multiplication-by-`3` pullback — the exact `n = 3` mirror of the merged `n = 2` finiteness gate
(`MulByTwoFinite.lean`,
`MulByTwoModuleFinite.lean`, `MulByTwoExtensionFinite.lean`, issue #421 Brick C).

## Main statements

* `WeierstrassCurve.Affine.CoordinateRing.mulByThreeEndo_isIntegralElem_genX`: the generic
  `x`-coordinate `genX = x(P)` is integral over the image of `mulByThreeEndo h2 h3`, a root of the
  **explicit monic degree-`9` polynomial** `Φ₃(genX ; T) - x(3 • P) · ΨSq₃(genX ; T)` whose
  coefficients lie in `[3]∗F(W)`. Monicity is because `Φ₃` has degree `9` with leading coefficient
  `1` (`coeff_Φ 3`) while `ΨSq₃` has degree `≤ 8` (`natDegree_ΨSq_le 3`).
* `WeierstrassCurve.Affine.CoordinateRing.mulByThreeRange_isIntegral_genX` / `_genY`: `genX` and
  `genY` are integral over `[3]∗F(W)` (`genY` by transitivity through the monic-in-`Y` Weierstrass
  equation over `[3]∗F(W)[genX]`).
* `WeierstrassCurve.Affine.CoordinateRing.isField_mulByThreeRange`: `[3]∗F(W)` is a field.
* `WeierstrassCurve.Affine.CoordinateRing.module_finite_mulByThreeRange`: `F(W)` is a **finite
  module** over `[3]∗F(W)`.

## Scope

This is the `n = 3` analogue of the merged `n = 2` bricks (#421). It uses only `[Field F]`,
`(2 : F) ≠ 0` and `(3 : F) ≠ 0`; Ward- and normality-independent, no `IsDedekindDomain` /
normality instance. The general bridge `isIntegral_range_of_isIntegralElem`
(`MulByTwoModuleFinite.lean`) is reused verbatim. The Dedekind integral-closure identification of
the `[3]∗` extension (subtle because `[3]∗F[W] ⊄ F[W]`, mirroring the `[2]∗` case) and the
downstream divisor pullback remain gated on the research-blocked normality gap (#396 Part A / #422).

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], II.2 (finite maps of curves),
  III.6, III.8.
-/

open Polynomial

namespace WeierstrassCurve.Affine
namespace CoordinateRing

open scoped Polynomial.Bivariate

variable {F : Type*} [Field F] {W : Affine F}

/-- The multiplication-by-`3` endomorphism fixes the base field `F ⊆ F(W)`: for `c : F`,
`[3]∗(c) = c`. (The pullback of a constant function is itself.) -/
lemma mulByThreeEndo_algebraMap_base (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (c : F) :
    mulByThreeEndo h2 h3 (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c := by
  have hst := IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField c
  rw [hst, mulByThreeEndo_algebraMap, mulByThreeCoordHom_algebraMap, ← hst]

/-- `[3]∗` composed with the base embedding `F → F(W)` is the base embedding: `[3]∗` fixes `F`. -/
lemma mulByThreeEndo_comp_algebraMap (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    (mulByThreeEndo h2 h3).comp (algebraMap F W.FunctionField) = algebraMap F W.FunctionField :=
  RingHom.ext (mulByThreeEndo_algebraMap_base h2 h3)

/-- Evaluating a base-changed univariate polynomial `q.map (F → F(W))` at `genX` through
`eval₂ (mulByThreeEndo h2 h3)` is the same as its ordinary evaluation, since `[3]∗` fixes the
(base-field) coefficients of `q.map`. -/
lemma eval₂_mulByThreeEndo_map (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (q : F[X]) :
    eval₂ (mulByThreeEndo h2 h3) (genX W) (q.map (algebraMap F W.FunctionField)) =
      (q.map (algebraMap F W.FunctionField)).eval (genX W) := by
  rw [eval₂_map, mulByThreeEndo_comp_algebraMap, ← eval_map]

/-- **The generic `x`-coordinate is integral over `[3]∗F(W)`.** `genX = x(P)` is a root of the monic
degree-`9` polynomial `Φ₃(genX ; T) - x(3 • P)·ΨSq₃(genX ; T)` (with coefficients in the image of
`mulByThreeEndo`), so `F(W)` is a degree-`≤ 9` integral extension of the multiplication-by-`3`
subfield `[3]∗F(W)`. -/
theorem mulByThreeEndo_isIntegralElem_genX (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    (mulByThreeEndo h2 h3).IsIntegralElem (genX W) := by
  set φ := algebraMap F W.FunctionField with hφ
  -- the denominator `ΨSq₃(genX)` does not vanish at the generic point
  have hden : ((W.map φ).ΨSq 3).eval (genX W) ≠ 0 := by
    have hsq := ψ_sq_evalEval (W := W.map φ) equation_gen 3
    rw [← hsq]
    exact pow_ne_zero 2 (psiThree_gen_ne h3)
  refine ⟨(W.map φ).Φ 3 - C (genX W) * (W.map φ).ΨSq 3, ?_, ?_⟩
  · -- the polynomial is monic: degree `≤ 9` with degree-`9` coefficient `1`
    apply monic_of_natDegree_le_of_coeff_eq_one 9
    · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact ((W.map φ).natDegree_Φ_le 3).trans (by decide)
      · exact (natDegree_C_mul_le _ _).trans (((W.map φ).natDegree_ΨSq_le 3).trans (by decide))
    · have hΨle : ((W.map φ).ΨSq 3).natDegree < (3 : ℤ).natAbs ^ 2 :=
        lt_of_le_of_lt ((W.map φ).natDegree_ΨSq_le 3) (by decide)
      rw [coeff_sub, coeff_C_mul, show (9 : ℕ) = (3 : ℤ).natAbs ^ 2 by decide,
        (W.map φ).coeff_Φ 3, coeff_eq_zero_of_natDegree_lt hΨle, mul_zero, sub_zero]
  · -- substituting `genX` gives `Φ₃(genX) - x(3 • P)·ΨSq₃(genX) = 0`
    have hEA : eval₂ (mulByThreeEndo h2 h3) (genX W) ((W.map φ).Φ 3) =
        ((W.map φ).Φ 3).eval (genX W) := by
      rw [hφ, map_Φ]; exact eval₂_mulByThreeEndo_map h2 h3 (W.Φ 3)
    have hEB : eval₂ (mulByThreeEndo h2 h3) (genX W) ((W.map φ).ΨSq 3) =
        ((W.map φ).ΨSq 3).eval (genX W) := by
      rw [hφ, map_ΨSq]; exact eval₂_mulByThreeEndo_map h2 h3 (W.ΨSq 3)
    rw [eval₂_sub, eval₂_mul, eval₂_C, hEA, hEB, mulByThreeEndo_genX h2 h3,
      div_mul_cancel₀ _ hden, sub_self]

/-- The base coordinates of `W ⁄ F(W)` lie in `[3]∗F(W)`: the pullback `[3]∗` fixes `F`, so each
`algebraMap F F(W) c` is in the range of `mulByThreeEndo`. -/
theorem algebraMap_mem_mulByThreeRange (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (c : F) :
    (algebraMap F W.FunctionField c) ∈ (mulByThreeEndo h2 h3).range :=
  ⟨algebraMap F W.FunctionField c, mulByThreeEndo_algebraMap_base h2 h3 c⟩

/-- **`genX` is integral over `[3]∗F(W)`.** The `IsIntegral`-over-range form of
`mulByThreeEndo_isIntegralElem_genX`. -/
theorem mulByThreeRange_isIntegral_genX (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    letI : Algebra ↥(mulByThreeEndo (W := W) h2 h3).range W.FunctionField :=
      ((mulByThreeEndo (W := W) h2 h3).range.subtype).toAlgebra
    IsIntegral ↥(mulByThreeEndo (W := W) h2 h3).range (genX W) :=
  isIntegral_range_of_isIntegralElem (mulByThreeEndo h2 h3)
    (mulByThreeEndo_isIntegralElem_genX h2 h3)

/-- **`genY` is integral over `[3]∗F(W)`.** It satisfies the monic-in-`Y` Weierstrass equation over
the intermediate ring `[3]∗F(W)[genX]`, and `genX` is integral over `[3]∗F(W)`, so transitivity of
integrality gives the claim. -/
theorem mulByThreeRange_isIntegral_genY (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    letI : Algebra ↥(mulByThreeEndo (W := W) h2 h3).range W.FunctionField :=
      ((mulByThreeEndo (W := W) h2 h3).range.subtype).toAlgebra
    IsIntegral ↥(mulByThreeEndo (W := W) h2 h3).range (genY W) := by
  letI : Algebra ↥(mulByThreeEndo (W := W) h2 h3).range W.FunctionField :=
    ((mulByThreeEndo (W := W) h2 h3).range.subtype).toAlgebra
  set φ := algebraMap F W.FunctionField with hφ
  have hgXA : IsIntegral ↥(mulByThreeEndo (W := W) h2 h3).range (genX W) :=
    mulByThreeRange_isIntegral_genX (W := W) h2 h3
  -- intermediate ring `B₀ = [3]∗F(W)[genX]`
  set B₀ := Algebra.adjoin ↥(mulByThreeEndo (W := W) h2 h3).range ({genX W} : Set W.FunctionField)
    with hB₀
  have hgXB : genX W ∈ B₀ := Algebra.subset_adjoin (Set.mem_singleton _)
  -- an element of `[3]∗F(W)` (viewed in `F(W)`) lies in `B₀`
  have hmemB : ∀ z : W.FunctionField, z ∈ (mulByThreeEndo (W := W) h2 h3).range → z ∈ B₀ :=
    fun z hz => by
      have h := B₀.algebraMap_mem (⟨z, hz⟩ : ↥(mulByThreeEndo (W := W) h2 h3).range)
      have he : (algebraMap ↥(mulByThreeEndo (W := W) h2 h3).range W.FunctionField)
          (⟨z, hz⟩ : ↥(mulByThreeEndo (W := W) h2 h3).range) = z := rfl
      rwa [he] at h
  have ha₁ : (W.map φ).a₁ ∈ B₀ := hmemB _ ⟨_, mulByThreeEndo_algebraMap_base h2 h3 W.a₁⟩
  have ha₂ : (W.map φ).a₂ ∈ B₀ := hmemB _ ⟨_, mulByThreeEndo_algebraMap_base h2 h3 W.a₂⟩
  have ha₃ : (W.map φ).a₃ ∈ B₀ := hmemB _ ⟨_, mulByThreeEndo_algebraMap_base h2 h3 W.a₃⟩
  have ha₄ : (W.map φ).a₄ ∈ B₀ := hmemB _ ⟨_, mulByThreeEndo_algebraMap_base h2 h3 W.a₄⟩
  have ha₆ : (W.map φ).a₆ ∈ B₀ := hmemB _ ⟨_, mulByThreeEndo_algebraMap_base h2 h3 W.a₆⟩
  -- the monic-in-`Y` Weierstrass relation at the generic point
  have hEq : (genY W) ^ 2 + ((W.map φ).a₁ * genX W + (W.map φ).a₃) * genY W
      + (-(genX W ^ 3 + (W.map φ).a₂ * genX W ^ 2 + (W.map φ).a₄ * genX W + (W.map φ).a₆)) = 0 := by
    have := ((W.map φ).equation_iff' (genX W) (genY W)).mp equation_gen
    linear_combination this
  -- coefficients of the monic quadratic, as elements of `B₀`
  set β : ↥B₀ := ⟨(W.map φ).a₁ * genX W + (W.map φ).a₃,
    add_mem (mul_mem ha₁ hgXB) ha₃⟩ with hβ
  set γ : ↥B₀ := ⟨-(genX W ^ 3 + (W.map φ).a₂ * genX W ^ 2 + (W.map φ).a₄ * genX W + (W.map φ).a₆),
    neg_mem (add_mem (add_mem (add_mem (pow_mem hgXB 3) (mul_mem ha₂ (pow_mem hgXB 2)))
      (mul_mem ha₄ hgXB)) ha₆)⟩ with hγ
  -- `genY` is integral over `B₀`
  have hgYB : IsIntegral ↥B₀ (genY W) := by
    refine ⟨X ^ 2 + (C β * X + C γ), monic_X_pow_add degree_linear_lt, ?_⟩
    have hβv : (algebraMap ↥B₀ W.FunctionField) β = (W.map φ).a₁ * genX W + (W.map φ).a₃ := rfl
    have hγv : (algebraMap ↥B₀ W.FunctionField) γ =
        -(genX W ^ 3 + (W.map φ).a₂ * genX W ^ 2 + (W.map φ).a₄ * genX W + (W.map φ).a₆) := rfl
    simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, hβv, hγv]
    linear_combination hEq
  -- transitivity: `Algebra.IsIntegral ↥A₀ ↥B₀` (adjoining the integral `genX`), then chain
  haveI hAB : Algebra.IsIntegral ↥(mulByThreeEndo (W := W) h2 h3).range ↥B₀ :=
    Algebra.IsIntegral.adjoin (fun x hx => by
      rw [Set.mem_singleton_iff] at hx; subst hx; exact hgXA)
  haveI : IsScalarTower ↥(mulByThreeEndo (W := W) h2 h3).range ↥B₀ W.FunctionField := inferInstance
  exact isIntegral_trans (genY W) hgYB

/-- **The multiplication-by-`3` subfield `[3]∗F(W)` is a field.** It is the range of the injective
field endomorphism `mulByThreeEndo h2 h3`, so every nonzero element `mulByThreeEndo w` has inverse
`mulByThreeEndo w⁻¹` inside the range. -/
theorem isField_mulByThreeRange (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    IsField ↥(mulByThreeEndo (W := W) h2 h3).range := by
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  rintro ⟨x, w, hw⟩ hx
  -- `x = mulByThreeEndo w`, and `x ≠ 0` gives `w ≠ 0`
  have hx0 : x ≠ 0 := by
    intro h; apply hx; exact Subtype.ext h
  have hw0 : w ≠ 0 := by
    intro h; apply hx0; rw [← hw, h, map_zero]
  refine ⟨⟨mulByThreeEndo h2 h3 w⁻¹, w⁻¹, rfl⟩, ?_⟩
  apply Subtype.ext
  change x * mulByThreeEndo h2 h3 w⁻¹ = 1
  rw [← hw, ← map_mul, mul_inv_cancel₀ hw0, map_one]

/-- **`F(W)` is a finite module over `[3]∗F(W)`.** Both generic coordinates are integral over the
subfield `[3]∗F(W)`, so the subalgebra they generate is a module-finite field, and (being a field
containing the coordinate ring `F[W]` inside the fraction field `F(W)`) it is all of `F(W)`. -/
theorem module_finite_mulByThreeRange (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    letI : Algebra ↥(mulByThreeEndo (W := W) h2 h3).range W.FunctionField :=
      ((mulByThreeEndo (W := W) h2 h3).range.subtype).toAlgebra
    Module.Finite ↥(mulByThreeEndo (W := W) h2 h3).range W.FunctionField := by
  letI : Algebra ↥(mulByThreeEndo (W := W) h2 h3).range W.FunctionField :=
    ((mulByThreeEndo (W := W) h2 h3).range.subtype).toAlgebra
  -- the two integrality facts
  have hIX : IsIntegral ↥(mulByThreeEndo (W := W) h2 h3).range (genX W) :=
    mulByThreeRange_isIntegral_genX (W := W) h2 h3
  have hIY : IsIntegral ↥(mulByThreeEndo (W := W) h2 h3).range (genY W) :=
    mulByThreeRange_isIntegral_genY (W := W) h2 h3
  -- the generated subalgebra `B = A₀[genX, genY]`
  set B := Algebra.adjoin ↥(mulByThreeEndo (W := W) h2 h3).range
    ({genX W, genY W} : Set W.FunctionField) with hB
  have hgenXB : genX W ∈ B := Algebra.subset_adjoin (by simp)
  have hgenYB : genY W ∈ B := Algebra.subset_adjoin (by simp)
  -- `B` is module-finite over `A₀`
  have hfinB : Module.Finite ↥(mulByThreeEndo (W := W) h2 h3).range ↥B := by
    apply Algebra.finite_adjoin_of_finite_of_isIntegral
      ((Set.finite_singleton (genY W)).insert (genX W))
    intro x hx
    rcases hx with hx | hx
    · rw [hx]; exact hIX
    · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hIY
  -- `A₀` is a field, hence `B` is a field (domain integral over a field)
  have hAfield : IsField ↥(mulByThreeEndo (W := W) h2 h3).range := isField_mulByThreeRange h2 h3
  haveI : Algebra.IsIntegral ↥(mulByThreeEndo (W := W) h2 h3).range ↥B :=
    Algebra.IsIntegral.of_finite (R := ↥(mulByThreeEndo (W := W) h2 h3).range) (B := ↥B)
  have hBfield : IsField ↥B := isField_of_isIntegral_of_isField' hAfield
  -- an element of `A₀` (viewed in `F(W)`) lies in `B`
  have hAB : ∀ z : W.FunctionField, z ∈ (mulByThreeEndo (W := W) h2 h3).range → z ∈ B := by
    intro z hz
    have h := B.algebraMap_mem (⟨z, hz⟩ : ↥(mulByThreeEndo (W := W) h2 h3).range)
    have he : (algebraMap ↥(mulByThreeEndo (W := W) h2 h3).range W.FunctionField)
        (⟨z, hz⟩ : ↥(mulByThreeEndo (W := W) h2 h3).range) = z := rfl
    rwa [he] at h
  -- `genPsi (mk (C a)) = algebraMap F[X] F(W) a`, and every `algebraMap F[X] F(W) a` lies in `B`
  have hmemX : ∀ a : F[X], algebraMap F[X] W.FunctionField a ∈ B := by
    intro a
    induction a using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial m c =>
        rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
        refine mul_mem ?_ (pow_mem ?_ m)
        · -- `algebraMap F[X] F(W) (C c) = algebraMap F F(W) c ∈ A₀ ⊆ B`
          have hCc : algebraMap F[X] W.FunctionField (C c) = algebraMap F W.FunctionField c := by
            rw [IsScalarTower.algebraMap_apply F F[X] W.FunctionField, Polynomial.algebraMap_eq]
          rw [hCc]
          exact hAB _ (algebraMap_mem_mulByThreeRange h2 h3 c)
        · -- `algebraMap F[X] F(W) X = genX ∈ B`
          have hX : algebraMap F[X] W.FunctionField X = genX W := by
            rw [genX, genPsi, show mk W (C X) = AdjoinRoot.of W.polynomial X from rfl,
              ← AdjoinRoot.algebraMap_eq,
              ← IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField]
          rw [hX]; exact hgenXB
  -- every image `genPsi (mk W p)` of the coordinate ring lies in `B`
  have hmemP : ∀ p : F[X][Y], genPsi W (mk W p) ∈ B := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, map_add]; exact add_mem hp hq
    | monomial n a =>
        rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, map_mul, map_pow]
        refine mul_mem ?_ (pow_mem ?_ n)
        · -- `genPsi (mk (C a)) = algebraMap F[X] F(W) a ∈ B`
          have hCa : genPsi W (mk W (C a)) = algebraMap F[X] W.FunctionField a := by
            rw [genPsi, show mk W (C a) = AdjoinRoot.of W.polynomial a from rfl,
              ← AdjoinRoot.algebraMap_eq,
              ← IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField]
          rw [hCa]; exact hmemX a
        · -- `genPsi (mk X) = genY ∈ B`
          have hXY : genPsi W (mk W X) = genY W := by
            rw [genY, AdjoinRoot.mk_X]
          rw [hXY]; exact hgenYB
  have hmem : ∀ c : W.CoordinateRing, genPsi W c ∈ B := by
    intro c
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective c
    exact hmemP p
  -- every element of `F(W)` lies in `B`, using that `B` is a field
  have hBtop : B = ⊤ := by
    rw [Algebra.eq_top_iff]
    intro z
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) z
    have hga : genPsi W a ∈ B := hmem a
    have hgb : genPsi W b ∈ B := hmem b
    -- `genPsi b ≠ 0`
    have hgb0 : genPsi W b ≠ 0 := by
      have : b ≠ 0 := nonZeroDivisors.ne_zero hb
      simpa [genPsi] using
        (map_ne_zero_iff _ (IsFractionRing.injective W.CoordinateRing W.FunctionField)).2 this
    -- invert `genPsi b` inside the field `B`
    obtain ⟨β', hβ'⟩ := hBfield.mul_inv_cancel (a := (⟨genPsi W b, hgb⟩ : ↥B))
      (by intro h; exact hgb0 (congrArg Subtype.val h))
    have hmul : genPsi W b * (β' : W.FunctionField) = 1 := congrArg Subtype.val hβ'
    have hinv : (genPsi W b)⁻¹ = (β' : W.FunctionField) := inv_eq_of_mul_eq_one_right hmul
    rw [← hab, div_eq_mul_inv, hinv]
    exact mul_mem hga (SetLike.coe_mem β')
  -- transport `Module.Finite A₀ B` along `B = ⊤ ≃ F(W)`
  rw [hBtop] at hfinB
  haveI := hfinB
  exact Module.Finite.equiv (Subalgebra.topEquiv.toLinearEquiv)

end CoordinateRing
end WeierstrassCurve.Affine
