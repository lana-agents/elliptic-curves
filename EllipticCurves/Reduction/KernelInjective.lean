/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Reduction.KernelSection

/-!
# Injectivity of the local parameter and the set bijection `E₁(K) ≃ 𝔪`

Let `R` be a **complete** discrete valuation ring (`IsAdicComplete (maximalIdeal R).asIdeal R`)
with fraction field `K = Frac R`, and let `W : WeierstrassCurve K` be an elliptic curve
(`W.IsElliptic`) with an integral model (`IsIntegral R W`).  The sibling file
`Reduction/KernelSection.lean` builds the section `pointOfParam : 𝔪 ∖ {0} → E₁(K)` and proves
**surjectivity** of the forward local parameter `zParam : E₁(K) → 𝔪`.  This file supplies the
complementary **injectivity**, closing the set-level bijection `E₁(K) ≃ 𝔪` (issue #361, rung 1 of
the remaining heart — the injectivity rung).

Injectivity is *purely algebraic* — it needs no new completeness/contraction machinery beyond what
`LocalParameterInverse.lean` already assumes.  The key fact is a **fixed-point uniqueness** for the
numeric Weierstrass functional equation in the maximal ideal:

* `wParam_unique` — if `w₁, w₂ ∈ 𝔪` both satisfy `w = z³ + (a₁z + a₂z²)w + (a₃ + a₄z)w² + a₆w³`
  for the same `z ∈ 𝔪`, then `w₁ = w₂`.  (Subtract the two equations, factor out `w₁ - w₂`, and
  observe the cofactor is a unit — it equals `1 - m` with `m ∈ 𝔪`.)

For a pole point `P = (x, y)` reducing to the origin, the value `w_P = -1/y` satisfies exactly this
functional equation (the reverse of `equation_xParam_yParam`), so `wParam` of its local parameter is
forced to be `w_P`, whence the recovered coordinates `(x(z), y(z))` are the original `(x, y)`.  Thus
`pointOfParam (zParam P) = P` and the local parameter is injective.

## Main results

* `WeierstrassCurve.wParam_unique` — uniqueness of the fixed point in `𝔪`.
* `WeierstrassCurve.eq_pointOfParam` — the section recovers the original point:
  `pointOfParam (localParamR P) = P` for a point reducing to the origin with nonzero parameter.
* `WeierstrassCurve.zParam_injective` — the local-parameter map `zParam : E₁(K) → 𝔪` is
  injective.
* `WeierstrassCurve.zParamEquiv` — the **set bijection** `E₁(K) ≃ 𝔪`.

## References

Silverman, *The Arithmetic of Elliptic Curves*, VII.2 Prop 2.2, IV.1.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### A congruence lemma for affine points -/

/-- Two affine points `some a b _` and `some x y _` are equal as soon as their coordinates agree;
the nonsingularity witnesses are propositionally irrelevant. -/
private theorem point_some_eq {W : WeierstrassCurve K} {a b x y : K}
    {ha : W.toAffine.Nonsingular a b} {hh : W.toAffine.Nonsingular x y}
    (hx : a = x) (hy : b = y) :
    (Affine.Point.some a b ha : W.toAffine.Point) = Affine.Point.some x y hh := by
  subst hx; subst hy; rfl

/-! ### Uniqueness of the numeric fixed point in the maximal ideal -/

omit [IsFractionRing R K] in
/-- **Fixed-point uniqueness for the Weierstrass functional equation in `𝔪`.**  If `w₁, w₂ ∈ 𝔪`
both satisfy `w = z³ + (a₁z + a₂z²)w + (a₃ + a₄z)w² + a₆w³` (integral-model coefficients) for the
same `z ∈ 𝔪`, then `w₁ = w₂`.  Subtracting the two equations factors as `(w₁ - w₂)·B = 0` where
`B = 1 - m` with `m ∈ 𝔪`; hence `B ∉ 𝔪`, so `B ≠ 0`, and the domain `R` forces `w₁ = w₂`. -/
theorem wParam_unique (W : WeierstrassCurve K) [IsIntegral R W] {z : R}
    (hz : z ∈ (maximalIdeal R).asIdeal) {w₁ w₂ : R}
    (hw₁ : w₁ ∈ (maximalIdeal R).asIdeal) (hw₂ : w₂ ∈ (maximalIdeal R).asIdeal)
    (he₁ : w₁ = z ^ 3
      + ((integralModel R W).a₁ * z + (integralModel R W).a₂ * z ^ 2) * w₁
      + ((integralModel R W).a₃ + (integralModel R W).a₄ * z) * w₁ ^ 2
      + (integralModel R W).a₆ * w₁ ^ 3)
    (he₂ : w₂ = z ^ 3
      + ((integralModel R W).a₁ * z + (integralModel R W).a₂ * z ^ 2) * w₂
      + ((integralModel R W).a₃ + (integralModel R W).a₄ * z) * w₂ ^ 2
      + (integralModel R W).a₆ * w₂ ^ 3) :
    w₁ = w₂ := by
  set α₁ := (integralModel R W).a₁
  set α₂ := (integralModel R W).a₂
  set α₃ := (integralModel R W).a₃
  set α₄ := (integralModel R W).a₄
  set α₆ := (integralModel R W).a₆
  set I := (maximalIdeal R).asIdeal
  -- Factor the difference of the two functional equations.
  have key : (w₁ - w₂)
      * (1 - (α₁ * z + α₂ * z ^ 2) - (α₃ + α₄ * z) * (w₁ + w₂)
          - α₆ * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)) = 0 := by
    linear_combination he₁ - he₂
  -- The cofactor `B` equals `1 - m` with `m ∈ 𝔪`, so `B ∉ 𝔪` and `B ≠ 0`.
  set B := 1 - (α₁ * z + α₂ * z ^ 2) - (α₃ + α₄ * z) * (w₁ + w₂)
      - α₆ * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2) with hB
  have hBmem : (1 : R) - B ∈ I := by
    have hrw : (1 : R) - B = z * (α₁ + α₂ * z)
        + w₁ * (α₃ + α₄ * z + α₆ * w₁ + α₆ * w₂) + w₂ * (α₃ + α₄ * z + α₆ * w₂) := by
      rw [hB]; ring
    rw [hrw]
    exact I.add_mem (I.add_mem (I.mul_mem_right _ hz) (I.mul_mem_right _ hw₁))
      (I.mul_mem_right _ hw₂)
  have hBne : B ≠ 0 := by
    intro h0
    refine (maximalIdeal R).isPrime.ne_top ?_
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : R) = 1 - B := by rw [h0, sub_zero]
    rw [h1]; exact hBmem
  rcases mul_eq_zero.mp key with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hBne

/-! ### The functional equation satisfied by `-1/y` -/

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- For a point `(x, y)` on the curve with `y ≠ 0`, the value `w = -1/y` satisfies the numeric
Weierstrass functional equation with parameter `z = -x/y`.  This is the reverse of
`equation_xParam_yParam`. -/
private theorem functional_eq_neg_inv_y (W : WeierstrassCurve K) [IsIntegral R W] {x y : K}
    (heqn : W.toAffine.Equation x y) (hy0 : y ≠ 0) :
    -1 / y = (-x / y) ^ 3
      + (W.a₁ * (-x / y) + W.a₂ * (-x / y) ^ 2) * (-1 / y)
      + (W.a₃ + W.a₄ * (-x / y)) * (-1 / y) ^ 2
      + W.a₆ * (-1 / y) ^ 3 := by
  rw [Affine.equation_iff] at heqn
  field_simp
  linear_combination -heqn

/-! ### The section recovers the original point -/

/-- The integral local parameter of a pole point is nonzero: `localParamR (some x y h) ≠ 0`. -/
theorem localParamR_ne_zero (W : WeierstrassCurve K) [IsIntegral R W] {x y : K}
    {h : W.toAffine.Nonsingular x y} (hx : 1 < valuation K (maximalIdeal R) x) :
    localParamR R W (.some x y h) ≠ 0 := by
  have hx0 : x ≠ 0 := (Valuation.ne_zero_iff _).mp (ne_of_gt (lt_trans one_pos hx))
  have hvy : 1 < valuation K (maximalIdeal R) y :=
    (valuation_pow_two_eq_pow_three_of_one_lt R W h.1 hx).1
  have hy0 : y ≠ 0 := (Valuation.ne_zero_iff _).mp (ne_of_gt (lt_trans one_pos hvy))
  have hne : localParam R W (.some x y h) ≠ 0 := by
    rw [localParam_some, if_pos hx]
    exact div_ne_zero (neg_ne_zero.mpr hx0) hy0
  intro h0
  exact hne (by rw [← algebraMap_localParamR, h0, map_zero])

/-- **The section recovers the original point.**  For a point `P` reducing to the origin with
nonzero local parameter, the coordinate expansion of `zParam P` returns `P` itself:
`pointOfParam (localParamR P) = P`.  This is the injectivity content: the coordinate expansion is
the two-sided inverse of the local parameter on the pole locus. -/
theorem eq_pointOfParam (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic]
    [IsAdicComplete (maximalIdeal R).asIdeal R]
    {P : W.toAffine.Point} (hP : ReducesToZero R W P) (hz0 : localParamR R W P ≠ 0) :
    pointOfParam R W (localParamR_mem R W hP) hz0 = P := by
  cases P with
  | zero => exact absurd (localParamR_zero R W) hz0
  | some x y h =>
    have hx : 1 < valuation K (maximalIdeal R) x := hP
    have heqn : W.toAffine.Equation x y := h.1
    have hvy : 1 < valuation K (maximalIdeal R) y :=
      (valuation_pow_two_eq_pow_three_of_one_lt R W heqn hx).1
    have hy0 : y ≠ 0 := (Valuation.ne_zero_iff _).mp (ne_of_gt (lt_trans one_pos hvy))
    have hvy_pos : 0 < valuation K (maximalIdeal R) y := lt_trans one_pos hvy
    -- Abbreviations: the parameter `z`, its membership, and `algebraMap z = -x/y`.
    set z := localParamR R W (.some x y h) with hzdef
    have hzmem : z ∈ (maximalIdeal R).asIdeal := localParamR_mem R W hP
    have hzK : algebraMap R K z = -x / y := by
      rw [hzdef, algebraMap_localParamR, localParam_some, if_pos hx]
    -- The lift `wPR ∈ R` of `-1/y`, in the maximal ideal.
    have hvle : valuation K (maximalIdeal R) (-1 / y) ≤ 1 := by
      rw [Valuation.map_div, Valuation.map_neg, map_one]
      exact (div_le_one₀ hvy_pos).mpr hvy.le
    have hvlt : valuation K (maximalIdeal R) (-1 / y) < 1 := by
      rw [Valuation.map_div, Valuation.map_neg, map_one]
      exact (div_lt_one₀ hvy_pos).mpr hvy
    obtain ⟨wPR, hwK⟩ := exists_lift_of_le_one hvle
    have hwPRmem : wPR ∈ (maximalIdeal R).asIdeal := by
      have hlt : valuation K (maximalIdeal R) (algebraMap R K wPR) < 1 := by rw [hwK]; exact hvlt
      exact (valuation_lt_one_iff_mem (K := K) (maximalIdeal R) wPR).mp hlt
    -- `wPR` satisfies the R-functional equation for `z`.
    have hR : wPR = z ^ 3 + ((integralModel R W).a₁ * z + (integralModel R W).a₂ * z ^ 2) * wPR
        + ((integralModel R W).a₃ + (integralModel R W).a₄ * z) * wPR ^ 2
        + (integralModel R W).a₆ * wPR ^ 3 := by
      apply IsFractionRing.injective R K
      simp only [map_add, map_mul, map_pow, hwK, hzK, integralModel_a₁_eq, integralModel_a₂_eq,
        integralModel_a₃_eq, integralModel_a₄_eq, integralModel_a₆_eq]
      exact functional_eq_neg_inv_y R W heqn hy0
    -- `wParam` of `z` is in the maximal ideal.
    have hwParammem : wParam R W hzmem ∈ (maximalIdeal R).asIdeal := by
      rw [wParam_eq_cube_mul]
      exact (maximalIdeal R).asIdeal.mul_mem_right _
        ((maximalIdeal R).asIdeal.pow_mem_of_mem hzmem 3 (by norm_num))
    -- Uniqueness forces `wParam = wPR`, hence `algebraMap (wParam) = -1/y`.
    have huniq : wParam R W hzmem = wPR :=
      wParam_unique R W hzmem hwParammem hwPRmem (wParam_functional_eq R W hzmem) hR
    have hwParamK : algebraMap R K (wParam R W hzmem) = -1 / y := by rw [huniq, hwK]
    -- The recovered coordinates are the original ones.
    have hxeq : xParam R W hzmem = x := by
      rw [xParam, hzK, hwParamK]; field_simp
    have hyeq : yParam R W hzmem = y := by
      rw [yParam, hwParamK]; field_simp
    rw [pointOfParam]
    exact point_some_eq hxeq hyeq

/-! ### Injectivity and the set bijection -/

open Classical in
/-- The set-theoretic inverse of the local parameter: `0 ↦ O`, and a nonzero `t ∈ 𝔪` maps to the
recovered point `pointOfParam t`. -/
noncomputable def paramInv (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic]
    [IsAdicComplete (maximalIdeal R).asIdeal R]
    (t : (maximalIdeal R).asIdeal) : {P : W.toAffine.Point // ReducesToZero R W P} :=
  if ht : (t : R) = 0 then ⟨.zero, reducesToZero_zero R W⟩
  else ⟨pointOfParam R W t.2 ht, reducesToZero_pointOfParam R W t.2 ht⟩

/-- `paramInv` is a left inverse of `zParam`: recovering the point from its parameter returns the
original point. -/
theorem paramInv_zParam (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic]
    [IsAdicComplete (maximalIdeal R).asIdeal R]
    (P : {P : W.toAffine.Point // ReducesToZero R W P}) :
    paramInv R W (zParam R W P) = P := by
  obtain ⟨P, hP⟩ := P
  cases P with
  | zero =>
    have h0 : ((zParam R W ⟨.zero, hP⟩ : (maximalIdeal R).asIdeal) : R) = 0 := by
      rw [zParam_coe]; exact localParamR_zero R W
    rw [paramInv, dif_pos h0]
  | some x y h =>
    have h0 : ((zParam R W ⟨.some x y h, hP⟩ : (maximalIdeal R).asIdeal) : R) ≠ 0 := by
      rw [zParam_coe]; exact localParamR_ne_zero R W hP
    rw [paramInv, dif_neg h0]
    exact Subtype.ext (eq_pointOfParam R W hP h0)

/-- **Injectivity of the local parameter** `zParam : E₁(K) → 𝔪`. -/
theorem zParam_injective (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic]
    [IsAdicComplete (maximalIdeal R).asIdeal R] :
    Function.Injective (zParam R W) :=
  Function.LeftInverse.injective (paramInv_zParam R W)

/-- **The set bijection `E₁(K) ≃ 𝔪`.**  The local parameter `z = -x/y` is a bijection between the
points reducing to the origin and the maximal ideal, assembling the surjectivity
(`zParam_surjective`) and injectivity (`zParam_injective`) rungs.  Endowing `𝔪` with the formal
group law `Ê(𝔪)` and proving `z` additive upgrades this to the group isomorphism `E₁(K) ≃+ Ê(𝔪)`. -/
noncomputable def zParamEquiv (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic]
    [IsAdicComplete (maximalIdeal R).asIdeal R] :
    {P : W.toAffine.Point // ReducesToZero R W P} ≃ (maximalIdeal R).asIdeal :=
  Equiv.ofBijective (zParam R W) ⟨zParam_injective R W, zParam_surjective R W⟩

end WeierstrassCurve
