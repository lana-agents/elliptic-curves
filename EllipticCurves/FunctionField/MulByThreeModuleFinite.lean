/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByThreeFinite
import EllipticCurves.FunctionField.MulByTwoModuleFinite

/-!
# Integrality of the generic `y`-coordinate over the multiplication-by-`3` subfield

Building on `mulByThreeEndo_isIntegralElem_genX`
(`EllipticCurves/FunctionField/MulByThreeFinite.lean`, issue #428, `n = 3` Brick C, first slice),
this file supplies the **second** half of the finiteness
gate for the multiplication-by-`3` pullback: the generic `y`-coordinate `genY = y(P)` is integral
over the image subfield `[3]∗F(W) = (mulByThreeEndo h2 h3).range` of `F(W)`. It is the `n = 3`
analogue of the merged `mulByTwoRange_isIntegral_genY` (`MulByTwoModuleFinite.lean`).

Where `genX` was integral *directly* (a root of an explicit monic degree-`9` polynomial with
coefficients in the image), `genY` is integral by **transitivity**: it satisfies the monic-in-`Y`
Weierstrass equation `genY² + (a₁·genX + a₃)·genY − (genX³ + a₂·genX² + a₄·genX + a₆) = 0`, whose
coefficients lie in the intermediate ring `[3]∗F(W)[genX]` (the base coordinates `aᵢ` are
`[3]∗`-fixed, being images of `F`), so `genY` is integral over `[3]∗F(W)[genX]`; and `genX` is
integral over `[3]∗F(W)`. Chaining these via `isIntegral_trans` gives integrality of `genY` over
`[3]∗F(W)`.

The general bridge `isIntegral_range_of_isIntegralElem` (from `RingHom.IsIntegralElem` to
`IsIntegral` over the range subring) is reused from `MulByTwoModuleFinite.lean` — it is stated for
an arbitrary ring endomorphism, so it applies verbatim to `mulByThreeEndo`.

## Main statements

* `WeierstrassCurve.Affine.CoordinateRing.mulByThreeRange_isIntegral_genX` /
  `mulByThreeRange_isIntegral_genY`: `genX` and `genY` are integral over `[3]∗F(W)`.

## Scope

This adds the `genY` half to the `genX` half of `MulByThreeFinite.lean`. Together they say both
generic coordinates are integral over `[3]∗F(W)`, feeding the module-finiteness gate
(`MulByThreeExtensionFinite.lean`). Only `[Field F]`, `(2 : F) ≠ 0` and `(3 : F) ≠ 0` are used;
Ward- and normality-independent.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], II.2, III.6, III.8.
-/

open Polynomial

namespace WeierstrassCurve.Affine
namespace CoordinateRing

open scoped Polynomial.Bivariate

variable {F : Type*} [Field F] {W : Affine F}

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

end CoordinateRing
end WeierstrassCurve.Affine
