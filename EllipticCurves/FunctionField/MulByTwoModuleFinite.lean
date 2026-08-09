/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByTwoFinite

/-!
# Integrality of the generic `y`-coordinate over the multiplication-by-`2` subfield

Building on `mulByTwoEndo_isIntegralElem_genX` (`EllipticCurves/FunctionField/MulByTwoFinite.lean`,
issue #421 Brick C, first slice), this file supplies the **second** half of the finiteness gate for
the multiplication-by-`2` pullback: the generic `y`-coordinate `genY = y(P)` is integral over the
image subfield `[2]∗F(W) = (mulByTwoEndo h2).range` of `F(W)`.

Where `genX` was integral *directly* (a root of an explicit monic quartic with coefficients in the
image), `genY` is integral by **transitivity**: it satisfies the monic-in-`Y` Weierstrass equation
`genY² + (a₁·genX + a₃)·genY − (genX³ + a₂·genX² + a₄·genX + a₆) = 0`, whose coefficients lie in the
intermediate ring `[2]∗F(W)[genX]` (the base coordinates `aᵢ` are `[2]∗`-fixed, being images of
`F`), so `genY` is integral over `[2]∗F(W)[genX]`; and `genX` is integral over `[2]∗F(W)`. Chaining
these via `isIntegral_trans` gives integrality of `genY` over `[2]∗F(W)`.

## Main statements

* `WeierstrassCurve.Affine.CoordinateRing.isIntegral_range_of_isIntegralElem`: the general bridge
  from `RingHom.IsIntegralElem` to `IsIntegral` over the range subring.
* `WeierstrassCurve.Affine.CoordinateRing.mulByTwoRange_isIntegral_genX` /
  `mulByTwoRange_isIntegral_genY`: `genX` and `genY` are integral over `[2]∗F(W)`.

## Scope

This adds the `genY` half to the merged `genX` half. Together they say both generic coordinates are
integral over `[2]∗F(W)`. The remaining Brick-C item — the full `Module.Finite ([2]∗F(W)) F(W)` /
`Algebra.IsIntegral` and the Dedekind-`B` identification (subtle because `[2]∗F[W] ⊄ F[W]`) — is
left for a follow-on; the two integrality facts here are its inputs (`F(W) = [2]∗F(W)[genX, genY]`
with both generators integral). Only `[Field F]` and `(2 : F) ≠ 0` are used; Ward- and
normality-independent.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], II.2, III.6, III.8.
-/

open Polynomial

namespace WeierstrassCurve.Affine
namespace CoordinateRing

open scoped Polynomial.Bivariate

variable {F : Type*} [Field F] {W : Affine F}

/-- **Bridge `RingHom.IsIntegralElem` → `IsIntegral` over the range subring.** If `x` is integral
with respect to a ring endomorphism `f` (a root of a monic polynomial evaluated through `f`), then
`x` is integral over the range subring `↥f.range` (with its natural algebra structure), since the
effective coefficients `f (pᵢ)` lie in `f.range`. -/
theorem isIntegral_range_of_isIntegralElem {A : Type*} [CommRing A]
    (f : A →+* A) {x : A} (hx : f.IsIntegralElem x) :
    letI := (f.range.subtype).toAlgebra; IsIntegral ↥f.range x := by
  letI := (f.range.subtype).toAlgebra
  obtain ⟨p, hpm, hpe⟩ := hx
  refine ⟨p.map f.rangeRestrict, hpm.map _, ?_⟩
  have hcomp : f.range.subtype.comp f.rangeRestrict = f := by ext a; rfl
  rw [RingHom.algebraMap_toAlgebra, eval₂_map, hcomp, hpe]

/-- The base coordinates of `W ⁄ F(W)` lie in `[2]∗F(W)`: the pullback `[2]∗` fixes `F`, so each
`algebraMap F F(W) c` is in the range of `mulByTwoEndo`. -/
theorem algebraMap_mem_mulByTwoRange (h2 : (2 : F) ≠ 0) (c : F) :
    (algebraMap F W.FunctionField c) ∈ (mulByTwoEndo h2).range :=
  ⟨algebraMap F W.FunctionField c, mulByTwoEndo_algebraMap_base h2 c⟩

/-- **`genX` is integral over `[2]∗F(W)`.** The `IsIntegral`-over-range form of the merged
`mulByTwoEndo_isIntegralElem_genX`. -/
theorem mulByTwoRange_isIntegral_genX (h2 : (2 : F) ≠ 0) :
    letI : Algebra ↥(mulByTwoEndo (W := W) h2).range W.FunctionField :=
      ((mulByTwoEndo (W := W) h2).range.subtype).toAlgebra
    IsIntegral ↥(mulByTwoEndo (W := W) h2).range (genX W) :=
  isIntegral_range_of_isIntegralElem (mulByTwoEndo h2) (mulByTwoEndo_isIntegralElem_genX h2)

/-- **`genY` is integral over `[2]∗F(W)`.** It satisfies the monic-in-`Y` Weierstrass equation over
the intermediate ring `[2]∗F(W)[genX]`, and `genX` is integral over `[2]∗F(W)`, so transitivity of
integrality gives the claim. -/
theorem mulByTwoRange_isIntegral_genY (h2 : (2 : F) ≠ 0) :
    letI : Algebra ↥(mulByTwoEndo (W := W) h2).range W.FunctionField :=
      ((mulByTwoEndo (W := W) h2).range.subtype).toAlgebra
    IsIntegral ↥(mulByTwoEndo (W := W) h2).range (genY W) := by
  letI : Algebra ↥(mulByTwoEndo (W := W) h2).range W.FunctionField :=
    ((mulByTwoEndo (W := W) h2).range.subtype).toAlgebra
  set φ := algebraMap F W.FunctionField with hφ
  have hgXA : IsIntegral ↥(mulByTwoEndo (W := W) h2).range (genX W) :=
    mulByTwoRange_isIntegral_genX (W := W) h2
  -- intermediate ring `B₀ = [2]∗F(W)[genX]`
  set B₀ := Algebra.adjoin ↥(mulByTwoEndo (W := W) h2).range ({genX W} : Set W.FunctionField)
    with hB₀
  have hgXB : genX W ∈ B₀ := Algebra.subset_adjoin (Set.mem_singleton _)
  -- an element of `[2]∗F(W)` (viewed in `F(W)`) lies in `B₀`
  have hmemB : ∀ z : W.FunctionField, z ∈ (mulByTwoEndo (W := W) h2).range → z ∈ B₀ :=
    fun z hz => by
      have h := B₀.algebraMap_mem (⟨z, hz⟩ : ↥(mulByTwoEndo (W := W) h2).range)
      have he : (algebraMap ↥(mulByTwoEndo (W := W) h2).range W.FunctionField)
          (⟨z, hz⟩ : ↥(mulByTwoEndo (W := W) h2).range) = z := rfl
      rwa [he] at h
  have ha₁ : (W.map φ).a₁ ∈ B₀ := hmemB _ ⟨_, mulByTwoEndo_algebraMap_base h2 W.a₁⟩
  have ha₂ : (W.map φ).a₂ ∈ B₀ := hmemB _ ⟨_, mulByTwoEndo_algebraMap_base h2 W.a₂⟩
  have ha₃ : (W.map φ).a₃ ∈ B₀ := hmemB _ ⟨_, mulByTwoEndo_algebraMap_base h2 W.a₃⟩
  have ha₄ : (W.map φ).a₄ ∈ B₀ := hmemB _ ⟨_, mulByTwoEndo_algebraMap_base h2 W.a₄⟩
  have ha₆ : (W.map φ).a₆ ∈ B₀ := hmemB _ ⟨_, mulByTwoEndo_algebraMap_base h2 W.a₆⟩
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
  haveI hAB : Algebra.IsIntegral ↥(mulByTwoEndo (W := W) h2).range ↥B₀ :=
    Algebra.IsIntegral.adjoin (fun x hx => by
      rw [Set.mem_singleton_iff] at hx; subst hx; exact hgXA)
  haveI : IsScalarTower ↥(mulByTwoEndo (W := W) h2).range ↥B₀ W.FunctionField := inferInstance
  exact isIntegral_trans (genY W) hgYB

end CoordinateRing
end WeierstrassCurve.Affine
