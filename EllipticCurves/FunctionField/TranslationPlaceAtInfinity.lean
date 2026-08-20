/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.PlaceOrder
import EllipticCurves.FunctionField.PointClosedPoint
import EllipticCurves.FunctionField.Places
import EllipticCurves.FunctionField.TranslationAutomorphism

/-!
# Where translation sends the point at infinity

`EllipticCurves.FunctionField.Places` shows that every `F`-algebra automorphism `σ` of `F(W)`
permutes the points of the projective curve, `mapProjPoint W σ : ProjPoint W ≃ ProjPoint W`, but
identifies that permutation for no `σ` at all.  This file identifies it for the translations
`τ_T = translateAlgEquiv h_T` (`EllipticCurves.FunctionField.TranslationAutomorphism`) at the one
point where the answer is not a triviality:

```lean
mapProjPoint W (translateAlgEquiv h₂) none = some (pointClosedPoint h₂')      -- h₂' is `-T`
mapProjPoint W (translateAlgEquiv h₂) (some (pointClosedPoint h₂)) = none
```

`EllipticCurves.FunctionField.GaloisFunctoriality` records the affine obstruction this answers:
`translateEndo` is *not* `IsFractionRing.ringEquivOfRingEquiv e` for a ring automorphism `e` of
`F[W]`, precisely because *"it moves the points at infinity"*.  That sentence was classical
background; here it becomes a theorem, and with it

```lean
mapProjPoint W (translateAlgEquiv h₂) ≠ Equiv.refl (ProjPoint W)
```

— the induced permutation is nontrivial.  This does **not** follow from `translateAlgEquiv_ne_one`:
a nontrivial automorphism could a priori fix every place.

## The computation, and why there is no shortcut

Write `X̂ = genX W`, `Ŷ = genY W`, `d = X̂ - x₂` and `s` for the secant slope, so `s * d = Ŷ - y₂`.
Both `ordInfty (s ^ 2) = -2` and `ordInfty X̂ = -2`, so the naive estimate on
`translateEndo h₂ X̂ = s ^ 2 + a₁ * s - a₂ - X̂ - x₂` gives only `ordInfty ≥ -2`: the leading terms
cancel, and the cancellation is the content.  Clearing the denominator exhibits it as a polynomial
identity in which the `X̂ ^ 3` terms cancel against `Ŷ ^ 2` (`translateEndo_genX_sub_mul_sq`), after
which the surviving element is `F`-linear in `X̂` and `Ŷ`, hence has `ordInfty ≥ -3`, hence

```lean
1 ≤ ordInfty W (translateEndo h₂ (genX W) - algebraMap F _ x₂)
```

The `y`-coordinate is **not** a corollary of the `x`-coordinate.  Both `y₂` and `negY x₂ y₂` are
roots of the reduced quadratic, so `x`-integrality plus the Weierstrass equation gives only the
dichotomy "the value at infinity is `y₂` or `negY x₂ y₂`"; choosing the branch is exactly the
content of `ordInfty_translateEndo_genY_sub` and needs its own identity.  (The reduction machinery
in `EllipticCurves.Reduction` is not a shortcut either: `redPt_add` carries
`[IsAdicComplete …]`, and the place at infinity is not complete.)

## Main results

* `WeierstrassCurve.Affine.ordInfty_translateEndo_genX_sub` and
  `WeierstrassCurve.Affine.ordInfty_translateEndo_genY_sub` — translation by `T` moves the generic
  point to a point congruent to `T` at infinity;
* **`WeierstrassCurve.Affine.mapProjPoint_translateAlgEquiv_none`** — the identification;
* `WeierstrassCurve.Affine.mapProjPoint_translateAlgEquiv_pointClosedPoint` and
  `WeierstrassCurve.Affine.mapProjPoint_translateAlgEquiv_ne_one` — the two corollaries;
* `WeierstrassCurve.Affine.divisorProj_translateEndo_none` and
  `WeierstrassCurve.Affine.divisorProj_translateEndo_pointClosedPoint` — the payoff, obtained by
  feeding the identification to `EllipticCurves.FunctionField.PlaceOrder`'s abstract transport.

## Implementation notes

The `ordInfty` lower bounds are proved by **membership in `ordInftyValuationSubring W`**, not by
iterating `le_ordInfty_add`: the latter carries three `≠ 0` side conditions per application and the
`F`-coefficients involved may vanish (they do, at `2`-torsion).  A valuation subring is a subring,
so a sum of members is a member with no side conditions at all; dividing by `Ŷ` (resp. `X̂ * Ŷ`)
turns the bound `-3 ≤ ordInfty` (resp. `-5 ≤ ordInfty`) into such a membership.

For the same reason the assembly phrases its targets as membership in `ValuationSubring.nonunits`
rather than as `0 < ordInfty`: `0` is a nonunit but has `ordInfty 0 = 0` by convention.

The `2`-torsion corner is not excluded anywhere: when `-T = T` the coefficient
`c₂ = negY x₂ y₂ - y₂` vanishes and every statement below still holds, reading
`mapProjPoint τ_T none = some (closed point of T)`.

## What is *not* here

* The action on affine points, `mapProjPoint (translateAlgEquiv h_T) (some (pointClosedPoint h_P))
  = some (pointClosedPoint h_{P ⊖ T})`.  That needs an evaluation-composition lemma
  (`(τ_{-T} f)(P) = f (P ⊖ T)` at the level of `evalEvalHom`), which does not exist yet.
* The transport of `divisorProj` along an arbitrary automorphism — that is
  `EllipticCurves.FunctionField.PlaceOrder`, which this file consumes rather than reproves.
* The action on *all* of `ProjPoint W`, and hence `#465` deliverable 2 in full: only the two orbits
  through the point at infinity are computed here.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.1–II.3, III.4.
* Stichtenoth, *Algebraic Function Fields and Codes*, I.1–I.4.
-/

open Polynomial IsDedekindDomain

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

/-! ### Lower bounds for `ordInfty`, via membership in the place at infinity -/

/-- If `g / u` is regular at infinity and `u` has a pole there, then `u`'s order bounds `g`'s from
below.  The hypothesis `ordInfty W u ≤ 0` is what covers the degenerate case `g = 0`, where the
convention `ordInfty 0 = 0` would otherwise break the conclusion. -/
theorem ordInfty_le_of_div_mem {u g : W.FunctionField} (hu : u ≠ 0) (hu0 : ordInfty W u ≤ 0)
    (h : g / u ∈ ordInftyValuationSubring W) : ordInfty W u ≤ ordInfty W g := by
  rcases eq_or_ne g 0 with rfl | hg
  · simpa using hu0
  · rw [mem_ordInftyValuationSubring, ordInfty_div hg hu] at h
    omega

/-- An `F`-linear combination of `1`, `genX` and `genY` has at worst a triple pole at infinity. -/
theorem neg_three_le_ordInfty_linear (c₀ c₁ c₂ : F) :
    (-3 : ℤ) ≤ ordInfty W (algebraMap F W.FunctionField c₀
      + algebraMap F W.FunctionField c₁ * genX W + algebraMap F W.FunctionField c₂ * genY W) := by
  have hY : genY W ≠ 0 := genY_ne_zero
  have hmem : (algebraMap F W.FunctionField c₀ + algebraMap F W.FunctionField c₁ * genX W
      + algebraMap F W.FunctionField c₂ * genY W) / genY W ∈ ordInftyValuationSubring W := by
    have hrw : (algebraMap F W.FunctionField c₀ + algebraMap F W.FunctionField c₁ * genX W
        + algebraMap F W.FunctionField c₂ * genY W) / genY W
        = algebraMap F W.FunctionField c₀ * (genY W)⁻¹
          + algebraMap F W.FunctionField c₁ * (genX W / genY W)
          + algebraMap F W.FunctionField c₂ := by
      field_simp
    rw [hrw]
    refine add_mem (add_mem (mul_mem (algebraMap_mem_ordInftyValuationSubring _) ?_)
        (mul_mem (algebraMap_mem_ordInftyValuationSubring _) ?_))
      (algebraMap_mem_ordInftyValuationSubring _)
    · simp [ordInfty_inv]
    · simp [ordInfty_genX_div_genY]
  have hle := ordInfty_le_of_div_mem hY (by simp) hmem
  rwa [ordInfty_genY] at hle

/-- An `F`-linear combination of `1`, `genX`, `genX ^ 2`, `genY` and `genX * genY` has at worst a
pole of order `5` at infinity. -/
theorem neg_five_le_ordInfty_quadratic (f₀ f₁ f₂ g₀ g₁ : F) :
    (-5 : ℤ) ≤ ordInfty W (algebraMap F W.FunctionField f₀
      + algebraMap F W.FunctionField f₁ * genX W
      + algebraMap F W.FunctionField f₂ * genX W ^ 2
      + algebraMap F W.FunctionField g₀ * genY W
      + algebraMap F W.FunctionField g₁ * genX W * genY W) := by
  have hX : genX W ≠ 0 := genX_ne_zero
  have hY : genY W ≠ 0 := genY_ne_zero
  have hXY : genX W * genY W ≠ 0 := mul_ne_zero hX hY
  have hord : ordInfty W (genX W * genY W) = -5 := by
    rw [ordInfty_mul hX hY, ordInfty_genX, ordInfty_genY]
    norm_num
  have hXinv : (genX W)⁻¹ ∈ ordInftyValuationSubring W := by simp [ordInfty_inv]
  have hYinv : (genY W)⁻¹ ∈ ordInftyValuationSubring W := by simp [ordInfty_inv]
  have hXYinv : (genX W * genY W)⁻¹ ∈ ordInftyValuationSubring W := by
    rw [mul_inv]
    exact mul_mem hXinv hYinv
  have hXdivY : genX W / genY W ∈ ordInftyValuationSubring W := by
    simp [ordInfty_genX_div_genY]
  have hmem : (algebraMap F W.FunctionField f₀ + algebraMap F W.FunctionField f₁ * genX W
      + algebraMap F W.FunctionField f₂ * genX W ^ 2
      + algebraMap F W.FunctionField g₀ * genY W
      + algebraMap F W.FunctionField g₁ * genX W * genY W) / (genX W * genY W)
      ∈ ordInftyValuationSubring W := by
    have hrw : (algebraMap F W.FunctionField f₀ + algebraMap F W.FunctionField f₁ * genX W
        + algebraMap F W.FunctionField f₂ * genX W ^ 2
        + algebraMap F W.FunctionField g₀ * genY W
        + algebraMap F W.FunctionField g₁ * genX W * genY W) / (genX W * genY W)
        = algebraMap F W.FunctionField f₀ * (genX W * genY W)⁻¹
          + algebraMap F W.FunctionField f₁ * (genY W)⁻¹
          + algebraMap F W.FunctionField f₂ * (genX W / genY W)
          + algebraMap F W.FunctionField g₀ * (genX W)⁻¹
          + algebraMap F W.FunctionField g₁ := by
      field_simp
    rw [hrw]
    exact add_mem (add_mem (add_mem (add_mem
      (mul_mem (algebraMap_mem_ordInftyValuationSubring _) hXYinv)
      (mul_mem (algebraMap_mem_ordInftyValuationSubring _) hYinv))
      (mul_mem (algebraMap_mem_ordInftyValuationSubring _) hXdivY))
      (mul_mem (algebraMap_mem_ordInftyValuationSubring _) hXinv))
      (algebraMap_mem_ordInftyValuationSubring _)
  have hle := ordInfty_le_of_div_mem hXY (by omega) hmem
  omega

/-- The image of the coordinate-ring generator `X - x₂` in `F(W)`. -/
theorem genX_sub_eq_genPsi_XClass (x₂ : F) :
    genX W - algebraMap F W.FunctionField x₂ = genPsi W (XClass W x₂) := by
  rw [XClass, Polynomial.C_sub, map_sub, map_sub, ← genX, ← genPsi_mk_CC (W := W) x₂]

/-- The image of the coordinate-ring generator `Y - y₂` in `F(W)`. -/
theorem genY_sub_eq_genPsi_YClass (y₂ : F) :
    genY W - algebraMap F W.FunctionField y₂ = genPsi W (YClass W (Polynomial.C y₂)) := by
  rw [YClass, map_sub, map_sub, genPsi_mk_CC]
  rfl

/-- The generic `x`-coordinate has a double pole at infinity, and translating it by a constant
does not change that. -/
theorem ordInfty_genX_sub (x₂ : F) :
    ordInfty W (genX W - algebraMap F W.FunctionField x₂) = -2 := by
  rw [genX_sub_eq_genPsi_XClass, genPsi, ordInfty_algebraMap (XClass_ne_zero x₂), XClass,
    deg_mk_C, Polynomial.natDegree_X_sub_C]
  norm_num

/-! ### The two coordinate identities -/

section Translation

variable [W.IsElliptic] {x₂ y₂ : F}

open Classical in
/-- **The `x`-coordinate identity.**  Clearing the denominator `(genX - x₂) ^ 2` out of
`translateEndo h₂ (genX W) - x₂` leaves something `F`-linear in `genX` and `genY`: the `genX ^ 3`
coming from `s ^ 2` (through the Weierstrass equation) cancels against the `genX * (genX - x₂) ^ 2`
of the addition formula, and the `genX ^ 2` terms cancel too.

This is the whole content of `ordInfty_translateEndo_genX_sub`; without it the naive estimate on
`s ^ 2 + a₁ * s - a₂ - genX - x₂` gives only `ordInfty ≥ -2`. -/
theorem translateEndo_genX_sub_mul_sq (h₂ : W.Equation x₂ y₂) :
    (translateEndo h₂ (genX W) - algebraMap F W.FunctionField x₂)
        * (genX W - algebraMap F W.FunctionField x₂) ^ 2
      = algebraMap F W.FunctionField (y₂ ^ 2 - 2 * x₂ ^ 3 + W.a₆ - W.a₂ * x₂ ^ 2 + W.a₁ * x₂ * y₂)
        + algebraMap F W.FunctionField (3 * x₂ ^ 2 + W.a₄ + 2 * W.a₂ * x₂ - W.a₁ * y₂) * genX W
        + algebraMap F W.FunctionField (-2 * y₂ - W.a₃ - W.a₁ * x₂) * genY W := by
  have hne : genX W ≠ algebraMap F W.FunctionField x₂ := genX_ne x₂
  have hd : genX W - algebraMap F W.FunctionField x₂ ≠ 0 := sub_ne_zero_of_ne hne
  have hs : (W.map (algebraMap F W.FunctionField)).slope (genX W)
        (algebraMap F W.FunctionField x₂) (genY W) (algebraMap F W.FunctionField y₂)
        * (genX W - algebraMap F W.FunctionField x₂)
      = genY W - algebraMap F W.FunctionField y₂ := by
    rw [Affine.slope_of_X_ne hne, div_mul_cancel₀ _ hd]
  have hgen := equation_gen (W := W)
  rw [Affine.equation_iff] at hgen
  rw [translateEndo_genX h₂]
  simp only [Affine.addX, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at hgen ⊢
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg]
  linear_combination ((W.map (algebraMap F W.FunctionField)).slope (genX W)
      (algebraMap F W.FunctionField x₂) (genY W) (algebraMap F W.FunctionField y₂)
      * (genX W - algebraMap F W.FunctionField x₂)
    + (genY W - algebraMap F W.FunctionField y₂)
    + algebraMap F W.FunctionField W.a₁ * (genX W - algebraMap F W.FunctionField x₂)) * hs + hgen

/-- **`translateEndo h₂` fixes the generic `x`-coordinate to first order at infinity**: the
`x`-coordinate of `𝒫 + 𝒯_T` specialises to `x₂` at the place at infinity. -/
theorem ordInfty_translateEndo_genX_sub (h₂ : W.Equation x₂ y₂) :
    1 ≤ ordInfty W (translateEndo h₂ (genX W) - algebraMap F W.FunctionField x₂) := by
  have hne : genX W ≠ algebraMap F W.FunctionField x₂ := genX_ne x₂
  have hd : genX W - algebraMap F W.FunctionField x₂ ≠ 0 := sub_ne_zero_of_ne hne
  have hdord : ordInfty W (genX W - algebraMap F W.FunctionField x₂) = -2 := ordInfty_genX_sub x₂
  have hsub : translateEndo h₂ (genX W) - algebraMap F W.FunctionField x₂ ≠ 0 :=
    sub_ne_zero_of_ne (translateEndo_genX_ne h₂ x₂)
  have hkey := translateEndo_genX_sub_mul_sq h₂
  have hbound := neg_three_le_ordInfty_linear (W := W)
    (y₂ ^ 2 - 2 * x₂ ^ 3 + W.a₆ - W.a₂ * x₂ ^ 2 + W.a₁ * x₂ * y₂)
    (3 * x₂ ^ 2 + W.a₄ + 2 * W.a₂ * x₂ - W.a₁ * y₂) (-2 * y₂ - W.a₃ - W.a₁ * x₂)
  rw [← hkey, ordInfty_mul hsub (pow_ne_zero 2 hd), ordInfty_pow, hdord] at hbound
  omega

open Classical in
/-- **The `y`-coordinate identity.**  The same denominator-clearing one degree up: after
substituting the `x`-coordinate identity, the surviving element is `F`-linear in
`1, genX, genX ^ 2, genY, genX * genY`. -/
theorem negAddY_sub_mul_cube (h₂ : W.Equation x₂ y₂) :
    ((W.map (algebraMap F W.FunctionField)).negAddY (genX W)
          (algebraMap F W.FunctionField x₂) (genY W)
          ((W.map (algebraMap F W.FunctionField)).slope (genX W)
            (algebraMap F W.FunctionField x₂) (genY W) (algebraMap F W.FunctionField y₂))
        - algebraMap F W.FunctionField (W.negY x₂ y₂))
        * (genX W - algebraMap F W.FunctionField x₂) ^ 3
      = (genY W - algebraMap F W.FunctionField y₂)
          * ((translateEndo h₂ (genX W) - algebraMap F W.FunctionField x₂)
            * (genX W - algebraMap F W.FunctionField x₂) ^ 2)
        - algebraMap F W.FunctionField (W.negY x₂ y₂ - y₂)
          * (genX W - algebraMap F W.FunctionField x₂) ^ 3 := by
  have hne : genX W ≠ algebraMap F W.FunctionField x₂ := genX_ne x₂
  have hd : genX W - algebraMap F W.FunctionField x₂ ≠ 0 := sub_ne_zero_of_ne hne
  have hs : (W.map (algebraMap F W.FunctionField)).slope (genX W)
        (algebraMap F W.FunctionField x₂) (genY W) (algebraMap F W.FunctionField y₂)
        * (genX W - algebraMap F W.FunctionField x₂)
      = genY W - algebraMap F W.FunctionField y₂ := by
    rw [Affine.slope_of_X_ne hne, div_mul_cancel₀ _ hd]
  rw [translateEndo_genX h₂]
  simp only [Affine.addX, Affine.negAddY, map_a₁, map_a₂]
  simp only [Affine.negY, map_sub, map_mul, map_neg]
  linear_combination ((genX W - algebraMap F W.FunctionField x₂) ^ 2
    * ((W.map (algebraMap F W.FunctionField)).slope (genX W)
        (algebraMap F W.FunctionField x₂) (genY W) (algebraMap F W.FunctionField y₂) ^ 2
      + algebraMap F W.FunctionField W.a₁
        * (W.map (algebraMap F W.FunctionField)).slope (genX W)
          (algebraMap F W.FunctionField x₂) (genY W) (algebraMap F W.FunctionField y₂)
      - algebraMap F W.FunctionField W.a₂ - genX W - algebraMap F W.FunctionField x₂
      - genX W)) * hs

open Classical in
/-- **`translateEndo h₂` fixes the generic `y`-coordinate to first order at infinity.**

This is *not* a corollary of `ordInfty_translateEndo_genX_sub`: both `y₂` and `negY x₂ y₂` are roots
of the quadratic that the reduced Weierstrass equation becomes once the `x`-coordinate is known, so
integrality in `x` gives only the dichotomy.  Choosing the branch is the content here, and it needs
the `y`-coordinate identity `negAddY_sub_mul_cube`. -/
theorem ordInfty_translateEndo_genY_sub (h₂ : W.Equation x₂ y₂) :
    1 ≤ ordInfty W (translateEndo h₂ (genY W) - algebraMap F W.FunctionField y₂) := by
  have hne : genX W ≠ algebraMap F W.FunctionField x₂ := genX_ne x₂
  have hd : genX W - algebraMap F W.FunctionField x₂ ≠ 0 := sub_ne_zero_of_ne hne
  -- `genY` is not a constant, so `translateEndo h₂ (genY W)` is not the constant `y₂`
  have hgenY_ne : genY W ≠ algebraMap F W.FunctionField y₂ := by
    intro h
    have h3 : ordInfty W (genY W) = -3 := ordInfty_genY
    rcases eq_or_ne y₂ 0 with rfl | hy
    · rw [h] at h3; simp at h3
    · rw [h, ordInfty_algebraMap_base hy] at h3; exact absurd h3 (by norm_num)
  have hsub : translateEndo h₂ (genY W) - algebraMap F W.FunctionField y₂ ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    refine hgenY_ne ((translateEndo h₂).injective ?_)
    rw [h, translateEndo_algebraMap_base]
  obtain ⟨c₀, hc₀⟩ : ∃ c : F,
      c = y₂ ^ 2 - 2 * x₂ ^ 3 + W.a₆ - W.a₂ * x₂ ^ 2 + W.a₁ * x₂ * y₂ := ⟨_, rfl⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c : F, c = 3 * x₂ ^ 2 + W.a₄ + 2 * W.a₂ * x₂ - W.a₁ * y₂ := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c : F, c = -2 * y₂ - W.a₃ - W.a₁ * x₂ := ⟨_, rfl⟩
  have hkey : (translateEndo h₂ (genY W) - algebraMap F W.FunctionField y₂)
        * (genX W - algebraMap F W.FunctionField x₂) ^ 3
      = algebraMap F W.FunctionField (-c₂ * (W.a₆ + x₂ ^ 3) + y₂ * c₀ + W.a₁ * c₀ * x₂)
        + algebraMap F W.FunctionField
            (-c₂ * (W.a₄ - 3 * x₂ ^ 2) + y₂ * c₁ - W.a₁ * c₀ + W.a₁ * c₁ * x₂) * genX W
        + algebraMap F W.FunctionField (-c₂ * (W.a₂ + 3 * x₂) - W.a₁ * c₁) * genX W ^ 2
        + algebraMap F W.FunctionField (-c₀ + c₂ * (y₂ + W.a₃) + W.a₁ * c₂ * x₂) * genY W
        + algebraMap F W.FunctionField (-c₁) * genX W * genY W := by
    subst hc₀ hc₁ hc₂
    have h1 := negAddY_sub_mul_cube h₂
    have h2 := translateEndo_genX_sub_mul_sq h₂
    have hgen := equation_gen (W := W)
    rw [Affine.equation_iff] at hgen
    have h3 : translateEndo h₂ (genY W)
        = -((W.map (algebraMap F W.FunctionField)).negAddY (genX W)
              (algebraMap F W.FunctionField x₂) (genY W)
              ((W.map (algebraMap F W.FunctionField)).slope (genX W)
                (algebraMap F W.FunctionField x₂) (genY W) (algebraMap F W.FunctionField y₂)))
            - algebraMap F W.FunctionField W.a₁ * translateEndo h₂ (genX W)
          - algebraMap F W.FunctionField W.a₃ := by
      rw [translateEndo_genY h₂, Affine.addY, Affine.negY, ← translateEndo_genX h₂]
      simp only [map_a₁, map_a₃]
    rw [h3]
    simp only [Affine.negY, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at h1 hgen ⊢
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg] at h1 h2 ⊢
    linear_combination (-1 : W.FunctionField) * h1
      + (-(genY W - algebraMap F W.FunctionField y₂)
        - algebraMap F W.FunctionField W.a₁
          * (genX W - algebraMap F W.FunctionField x₂)) * h2
      + (2 * algebraMap F W.FunctionField y₂ + algebraMap F W.FunctionField W.a₃
        + algebraMap F W.FunctionField W.a₁ * algebraMap F W.FunctionField x₂) * hgen
  have hbound := neg_five_le_ordInfty_quadratic (W := W)
    (-c₂ * (W.a₆ + x₂ ^ 3) + y₂ * c₀ + W.a₁ * c₀ * x₂)
    (-c₂ * (W.a₄ - 3 * x₂ ^ 2) + y₂ * c₁ - W.a₁ * c₀ + W.a₁ * c₁ * x₂)
    (-c₂ * (W.a₂ + 3 * x₂) - W.a₁ * c₁)
    (-c₀ + c₂ * (y₂ + W.a₃) + W.a₁ * c₂ * x₂) (-c₁)
  rw [← hkey, ordInfty_mul hsub (pow_ne_zero 3 hd), ordInfty_pow, ordInfty_genX_sub] at hbound
  omega

end Translation

/-! ### The identification -/

section Assembly

variable [W.IsElliptic] [IsDedekindDomain W.CoordinateRing] {x₂ y₂ : F}

/-- **Translation by `T` sends the point at infinity to the closed point of `-T`.**

Reading `τ_T` as `f ↦ f ∘ (· + T)`, its inverse is `τ_{-T}`, and a function is regular at infinity
after pulling back along `τ_{-T}` exactly when it is regular at `-T`.  Formally: the place
`(ordInftyValuationSubring W).comap τ_{-T}` contains `F` and `genX W`, so rung 4 presents it as
`R_v` for a height-one prime `v` of `F[W]`; both generators of the closed point of `-T` land in the
nonunits of that place by `ordInfty_translateEndo_genX_sub` / `ordInfty_translateEndo_genY_sub`;
and two maximal ideals with one contained in the other are equal.

This is the theorem behind the docstring remark in
`EllipticCurves.FunctionField.GaloisFunctoriality` that `translateEndo` *"moves the points at
infinity"* — until rung 4 that sentence could not be stated, only asserted. -/
theorem mapProjPoint_translateAlgEquiv_none (h₂ : W.Equation x₂ y₂) :
    mapProjPoint W (translateAlgEquiv h₂) none
      = some (pointClosedPoint ((W.equation_neg x₂ y₂).mpr h₂)) := by
  set h₂' := (W.equation_neg x₂ y₂).mpr h₂ with hh₂'
  set σ : W.FunctionField ≃ₐ[F] W.FunctionField := translateAlgEquiv h₂ with hσ
  have hsymm : ∀ g : W.FunctionField,
      (σ.symm : W.FunctionField →+* W.FunctionField) g = translateEndo h₂' g := fun g =>
    translateAlgEquiv_symm_apply h₂ g
  -- the transported place at infinity
  set S : ValuationSubring W.FunctionField :=
    (ordInftyValuationSubring W).comap (σ.symm : W.FunctionField →+* W.FunctionField) with hS
  have htop : ordInftyValuationSubring W ≠ ⊤ := fun h =>
    genX_notMem_ordInftyValuationSubring (h ▸ ValuationSubring.mem_top _)
  have hStop : S ≠ ⊤ := comap_algEquiv_ne_top σ.symm htop
  have hSF : ∀ c : F, algebraMap F W.FunctionField c ∈ S :=
    algebraMap_mem_comap_algEquiv σ.symm algebraMap_mem_ordInftyValuationSubring
  have hSX : genX W ∈ S := by
    rw [hS, ValuationSubring.mem_comap, hsymm]
    have hb := ordInfty_translateEndo_genX_sub h₂'
    have : translateEndo h₂' (genX W)
        = (translateEndo h₂' (genX W) - algebraMap F W.FunctionField x₂)
          + algebraMap F W.FunctionField x₂ := by ring
    rw [this]
    exact add_mem (by rw [mem_ordInftyValuationSubring]; omega)
      (algebraMap_mem_ordInftyValuationSubring x₂)
  -- membership in the nonunits of `S` is a zero at infinity after transport
  have hSnonunits : ∀ f : W.FunctionField, 1 ≤ ordInfty W (translateEndo h₂' f) →
      f ∈ S.nonunits := by
    intro f hf
    rw [ValuationSubring.mem_nonunits_iff_or]
    refine Or.inr fun hmem => ?_
    rw [hS, ValuationSubring.mem_comap, hsymm, map_inv₀, mem_ordInftyValuationSubring,
      ordInfty_inv] at hmem
    omega
  obtain ⟨v, hv⟩ := exists_heightOneSpectrum_of_genX_mem hSF hStop hSX
  refine (mapProjPoint_eq_iff σ).mpr ?_
  rw [placeOf_some, placeOf_none, ← hS, ← hv]
  congr 1
  refine (HeightOneSpectrum.ext ?_).symm
  refine ((XYIdeal_isMaximal h₂').eq_of_le v.isPrime.ne_top ?_).symm
  rw [XYIdeal, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  constructor
  · rw [SetLike.mem_coe, HeightOneSpectrum.mem_asIdeal_iff_mem_nonunits (K := W.FunctionField),
      hv, ← genPsi, ← genX_sub_eq_genPsi_XClass]
    refine hSnonunits _ ?_
    rw [map_sub, translateEndo_algebraMap_base]
    exact ordInfty_translateEndo_genX_sub h₂'
  · rw [SetLike.mem_coe, HeightOneSpectrum.mem_asIdeal_iff_mem_nonunits (K := W.FunctionField),
      hv, ← genPsi, ← genY_sub_eq_genPsi_YClass]
    refine hSnonunits _ ?_
    rw [map_sub, translateEndo_algebraMap_base]
    exact ordInfty_translateEndo_genY_sub h₂'

omit [IsDedekindDomain W.CoordinateRing] in
/-- `τ_{-T}` is the inverse of `τ_T`, as `F`-algebra automorphisms. -/
theorem translateAlgEquiv_equation_neg (h₂ : W.Equation x₂ y₂) :
    translateAlgEquiv ((W.equation_neg x₂ y₂).mpr h₂) = (translateAlgEquiv h₂).symm :=
  AlgEquiv.ext fun g => by rw [translateAlgEquiv_apply, translateAlgEquiv_symm_apply]

/-- **Translation by `T` sends the closed point of `T` to the point at infinity** — the other half
of "`τ_T` moves the points at infinity".  Formally it is
`mapProjPoint_translateAlgEquiv_none` at `-T`, read through
`mapProjPoint W σ⁻¹ = (mapProjPoint W σ)⁻¹`, which holds because `mapProjPointHom` is a monoid
homomorphism. -/
theorem mapProjPoint_translateAlgEquiv_pointClosedPoint (h₂ : W.Equation x₂ y₂) :
    mapProjPoint W (translateAlgEquiv h₂) (some (pointClosedPoint h₂)) = none := by
  have key := mapProjPoint_translateAlgEquiv_none ((W.equation_neg x₂ y₂).mpr h₂)
  have hpt : pointClosedPoint ((W.equation_neg x₂ (W.negY x₂ y₂)).mpr
      ((W.equation_neg x₂ y₂).mpr h₂)) = pointClosedPoint h₂ := by
    refine HeightOneSpectrum.ext ?_
    simp only [pointClosedPoint_asIdeal, negY_negY]
  rw [hpt, translateAlgEquiv_equation_neg h₂] at key
  have hinv : mapProjPoint W (translateAlgEquiv h₂).symm
      = (mapProjPoint W (translateAlgEquiv h₂)).symm := by
    have h := map_inv (mapProjPointHom W) (translateAlgEquiv h₂)
    simp only [mapProjPointHom_apply] at h
    exact h
  rw [hinv] at key
  exact ((mapProjPoint W (translateAlgEquiv h₂)).symm_apply_eq).mp key |>.symm

/-- **The permutation induced by a translation is not the identity.**

This is strictly stronger than `translateAlgEquiv_ne_one`: an automorphism that is not the identity
could a priori still fix every place.  Note the standing caveat, inherited from
`EllipticCurves.FunctionField.TranslationAutomorphism`: this needs `W` to have an affine `F`-point,
which is a condition on `F` and is not asserted here. -/
theorem mapProjPoint_translateAlgEquiv_ne_one (h₂ : W.Equation x₂ y₂) :
    mapProjPoint W (translateAlgEquiv h₂) ≠ Equiv.refl (ProjPoint W) := by
  intro h
  have key := mapProjPoint_translateAlgEquiv_none h₂
  rw [h, Equiv.refl_apply] at key
  simp at key

/-! ### The payoff -/

/-- **The order of vanishing of `τ_T f` at infinity is the order of `f` at `T`.**  The abstract
transport `divisorProj_algEquiv_apply` (`EllipticCurves.FunctionField.PlaceOrder`) says the two
agree along `mapProjPoint`; this file supplies which point that is. -/
theorem divisorProj_translateEndo_none (h₂ : W.Equation x₂ y₂) {f : W.FunctionField} (hf : f ≠ 0) :
    divisorProj W (translateEndo h₂ f) none = divisorProj W f (some (pointClosedPoint h₂)) := by
  have h := divisorProj_algEquiv_apply (translateAlgEquiv h₂) hf (some (pointClosedPoint h₂))
  rwa [mapProjPoint_translateAlgEquiv_pointClosedPoint, translateAlgEquiv_apply] at h

/-- **The order of vanishing of `τ_T f` at `-T` is the order of `f` at infinity.** -/
theorem divisorProj_translateEndo_pointClosedPoint (h₂ : W.Equation x₂ y₂)
    {f : W.FunctionField} (hf : f ≠ 0) :
    divisorProj W (translateEndo h₂ f) (some (pointClosedPoint ((W.equation_neg x₂ y₂).mpr h₂)))
      = divisorProj W f none := by
  have h := divisorProj_algEquiv_apply (translateAlgEquiv h₂) hf none
  rwa [mapProjPoint_translateAlgEquiv_none, translateAlgEquiv_apply] at h

end Assembly

end WeierstrassCurve.Affine
