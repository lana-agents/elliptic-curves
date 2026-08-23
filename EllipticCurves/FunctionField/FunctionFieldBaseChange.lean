/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByThreeEndomorphism
import EllipticCurves.FunctionField.MulByTwoEndomorphism

/-!
# Base change of the function field of a Weierstrass curve

Let `W` be a Weierstrass curve over a field `F` and let `K` be a field that is an `F`-algebra.
`EllipticCurves/FunctionField/CoordinateRingBaseChange.lean` base-changes the *coordinate ring*;
this file base-changes the *function field*, and transports the three ring endomorphisms of `F(W)`
that the divisor-theoretic Weil pairing is built from.

* `functionFieldMap W K : F(W) →+* K(W⁄K)`, obtained from Mathlib's coordinate-ring map
  `CoordinateRing.map W (algebraMap F K)` — which is injective because `F → K` is
  (`CoordinateRing.map_injective`) — by the universal property of the fraction field. It is
  automatically **injective**, being a homomorphism of fields.

* the transport of the two coordinate generators, `functionFieldMap_genX` / `functionFieldMap_genY`,
  and of the base field, `functionFieldMap_algebraMap_base`. Together these say that the
  base-changed curve over `K(W⁄K)` is the pushforward of the curve over `F(W)`
  (`map_map_functionFieldMap`), which is what makes every coordinate formula transportable.

* **intertwining** of the endomorphisms of the function field with base change:
  `functionFieldMap_translateEndo`, `functionFieldMap_mulByTwoEndo`,
  `functionFieldMap_mulByThreeEndo`.

## Why this is wanted

Every rung-6 Weil-pairing statement in this tree currently carries `[IsAlgClosed F]`, because the
geometric inputs (`hprin`, and the halving point `P` with `[n]P = T`) are only available over `F̄`.
The `∀ g` root-independent forms of those statements are equalities in `F(W)` — and an equality in
`F(W)` may be checked after an **injective** map to `F̄(W⁄F̄)`. So the F̄-statements descend to a
general base field once each construction they mention is known to commute with base change. This
file supplies that for the three endomorphisms; the divisor-level compatibilities remain.

## Design notes

* No `Algebra F(W) K(W⁄K)` instance is registered: `functionFieldMap` is a bare `→+*`, and the
  interaction with the base field is recorded by the explicit lemma
  `functionFieldMap_algebraMap_base` rather than by a scalar tower. This keeps the file free of
  instance diamonds on `FunctionField`, which carries several algebra structures already
  (`RatFuncExtension.lean` documents one of them).

* The characteristic hypotheses of `mulByTwoEndo` / `mulByThreeEndo` are taken **twice**, once over
  `F` and once over `K` (`h2` and `h2'`), rather than deriving the second from the first inside the
  statement. `algebraMap_ofNat_ne_zero` is provided for producing the second.

## Main definitions and statements

* `WeierstrassCurve.Affine.CoordinateRing.functionFieldMap` and
  `functionFieldMap_injective`.
* `functionFieldMap_algebraMap`, `functionFieldMap_algebraMap_base`, `functionFieldMap_genX`,
  `functionFieldMap_genY`, `map_map_functionFieldMap`.
* `functionFieldMap_translateEndo`, `functionFieldMap_mulByTwoEndo`,
  `functionFieldMap_mulByThreeEndo`.

## Remaining work

The divisor-level compatibilities — `divisor`, `divisorProj`, and hence `weilPairingElt` — are not
here. They are not coordinate computations: they need the behaviour of `functionFieldMap` on the
places of `F(W)`, which is a genuinely different argument. A `Point.map` bridge identifying the
base-changed torsion point with the image of the original is likewise still missing; the analogous
gadget for `F → F(W)` is `torsionPointMap` (`TranslationTorsionMap.lean`).

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8 (the Weil pairing).
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine
namespace CoordinateRing

variable {F : Type*} [Field F] (W : Affine F) (K : Type*) [Field K] [Algebra F K]

/-! ## The base-change map on function fields -/

variable {W K} in
/-- A numeral that is nonzero in `F` stays nonzero in a field extension `K`. This is what turns the
characteristic hypotheses of `mulByTwoEndo` / `mulByThreeEndo` over `F` into their counterparts
over `K`. -/
theorem algebraMap_ofNat_ne_zero {n : ℕ} [n.AtLeastTwo] (h : (OfNat.ofNat n : F) ≠ 0) :
    (OfNat.ofNat n : K) ≠ 0 := by
  rw [← map_ofNat (algebraMap F K) n, ne_eq, map_eq_zero]
  exact h

/-- Base change of the coordinate ring along `F → K` is injective, because `F → K` is. -/
theorem map_algebraMap_injective :
    Function.Injective (CoordinateRing.map W (algebraMap F K)) :=
  CoordinateRing.map_injective (algebraMap F K).injective

/-- `F[W] → K[W⁄K] → K(W⁄K)` is injective, which is what `IsFractionRing.lift` consumes. -/
theorem genPsi_comp_map_injective :
    Function.Injective
      ((genPsi (W.map (algebraMap F K))).comp (CoordinateRing.map W (algebraMap F K))) := by
  rw [RingHom.coe_comp]
  exact (IsFractionRing.injective _ _).comp (map_algebraMap_injective W K)

/-- **The base-change map on function fields** `F(W) →+* K(W⁄K)`, extending Mathlib's
coordinate-ring map `CoordinateRing.map W (algebraMap F K)` along the universal property of the
fraction field. -/
noncomputable def functionFieldMap :
    W.FunctionField →+* (W.map (algebraMap F K)).FunctionField :=
  IsFractionRing.lift (genPsi_comp_map_injective W K)

/-- On the image of `F[W]`, `functionFieldMap` is the coordinate-ring base-change map. -/
@[simp]
theorem functionFieldMap_algebraMap (a : W.CoordinateRing) :
    functionFieldMap W K (genPsi W a)
      = genPsi (W.map (algebraMap F K)) (CoordinateRing.map W (algebraMap F K) a) :=
  IsFractionRing.lift_algebraMap _ a

/-- **The base-change map is injective**, being a ring homomorphism out of a field. This is the
whole point of the file: an equality in `F(W)` may be proved after mapping to `K(W⁄K)`. -/
theorem functionFieldMap_injective : Function.Injective (functionFieldMap W K) :=
  (functionFieldMap W K).injective

/-- Base change fixes the generic `x`-coordinate. -/
@[simp]
theorem functionFieldMap_genX :
    functionFieldMap W K (genX W) = genX (W.map (algebraMap F K)) := by
  rw [genX, functionFieldMap_algebraMap, genX, CoordinateRing.map_mk]
  simp

/-- Base change fixes the generic `y`-coordinate. -/
@[simp]
theorem functionFieldMap_genY :
    functionFieldMap W K (genY W) = genY (W.map (algebraMap F K)) := by
  rw [genY, functionFieldMap_algebraMap, genY, CoordinateRing.map, AdjoinRoot.lift_root]

/-- On the base field, `functionFieldMap` is `algebraMap F K`. -/
theorem functionFieldMap_algebraMap_base (c : F) :
    functionFieldMap W K (algebraMap F W.FunctionField c)
      = algebraMap K (W.map (algebraMap F K)).FunctionField (algebraMap F K c) := by
  rw [← genPsi_mk_CC, functionFieldMap_algebraMap, CoordinateRing.map_mk]
  simp only [Polynomial.map_C, Polynomial.coe_mapRingHom]
  exact genPsi_mk_CC _

/-- **The curve transports.** `W ⁄ F(W)` pushed forward along the base-change map is `W⁄K ⁄ K(W⁄K)`.
Every coordinate formula below is transported through this one equation. -/
theorem map_map_functionFieldMap :
    (W.map (algebraMap F W.FunctionField)).map (functionFieldMap W K)
      = (W.map (algebraMap F K)).map
          (algebraMap K (W.map (algebraMap F K)).FunctionField) := by
  have h : (functionFieldMap W K).comp (algebraMap F W.FunctionField)
      = (algebraMap K (W.map (algebraMap F K)).FunctionField).comp (algebraMap F K) :=
    RingHom.ext fun c => functionFieldMap_algebraMap_base W K c
  exact congrArg W.map h

variable {W K}

/-! ## The multiplication-by-`n` endomorphisms

`mulByTwoEndo` and `mulByThreeEndo` send the coordinate generators to division-polynomial
expressions in `genX` and `genY`, so the transports below are exactly what is needed to push them
through the base-change map.
-/

/-- Transport of a univariate evaluation at the generic `x`-coordinate. -/
private lemma functionFieldMap_eval_genX (p : W.FunctionField[X]) :
    functionFieldMap W K (p.eval (genX W))
      = (p.map (functionFieldMap W K)).eval (genX (W.map (algebraMap F K))) := by
  rw [← functionFieldMap_genX W K]
  exact (Polynomial.eval_map_apply ..).symm

/-- Transport of a bivariate evaluation at the generic point. -/
private lemma functionFieldMap_evalEval_gen (q : W.FunctionField[X][Y]) :
    functionFieldMap W K (q.evalEval (genX W) (genY W))
      = (q.map (mapRingHom (functionFieldMap W K))).evalEval
          (genX (W.map (algebraMap F K))) (genY (W.map (algebraMap F K))) := by
  rw [← functionFieldMap_genX W K, ← functionFieldMap_genY W K]
  exact (Polynomial.map_mapRingHom_evalEval ..).symm

@[simp]
theorem functionFieldMap_map_a₁ :
    functionFieldMap W K (W.map (algebraMap F W.FunctionField)).a₁
      = ((W.map (algebraMap F K)).map
          (algebraMap K (W.map (algebraMap F K)).FunctionField)).a₁ := by
  rw [← map_map_functionFieldMap]
  exact (WeierstrassCurve.map_a₁ ..).symm

@[simp]
theorem functionFieldMap_map_a₃ :
    functionFieldMap W K (W.map (algebraMap F W.FunctionField)).a₃
      = ((W.map (algebraMap F K)).map
          (algebraMap K (W.map (algebraMap F K)).FunctionField)).a₃ := by
  rw [← map_map_functionFieldMap]
  exact (WeierstrassCurve.map_a₃ ..).symm

@[simp]
theorem functionFieldMap_Φ_eval (n : ℤ) :
    functionFieldMap W K (((W.map (algebraMap F W.FunctionField)).Φ n).eval (genX W))
      = (((W.map (algebraMap F K)).map
          (algebraMap K (W.map (algebraMap F K)).FunctionField)).Φ n).eval
            (genX (W.map (algebraMap F K))) := by
  conv_rhs => rw [← map_map_functionFieldMap, WeierstrassCurve.map_Φ]
  rw [functionFieldMap_eval_genX]

@[simp]
theorem functionFieldMap_Ψ₂Sq_eval :
    functionFieldMap W K ((W.map (algebraMap F W.FunctionField)).Ψ₂Sq.eval (genX W))
      = ((W.map (algebraMap F K)).map
          (algebraMap K (W.map (algebraMap F K)).FunctionField)).Ψ₂Sq.eval
            (genX (W.map (algebraMap F K))) := by
  conv_rhs => rw [← map_map_functionFieldMap, WeierstrassCurve.map_Ψ₂Sq]
  rw [functionFieldMap_eval_genX]

@[simp]
theorem functionFieldMap_ΨSq_eval (n : ℤ) :
    functionFieldMap W K (((W.map (algebraMap F W.FunctionField)).ΨSq n).eval (genX W))
      = (((W.map (algebraMap F K)).map
          (algebraMap K (W.map (algebraMap F K)).FunctionField)).ΨSq n).eval
            (genX (W.map (algebraMap F K))) := by
  conv_rhs => rw [← map_map_functionFieldMap, WeierstrassCurve.map_ΨSq]
  rw [functionFieldMap_eval_genX]

@[simp]
theorem functionFieldMap_preΨ₄_eval :
    functionFieldMap W K ((W.map (algebraMap F W.FunctionField)).preΨ₄.eval (genX W))
      = ((W.map (algebraMap F K)).map
          (algebraMap K (W.map (algebraMap F K)).FunctionField)).preΨ₄.eval
            (genX (W.map (algebraMap F K))) := by
  conv_rhs => rw [← map_map_functionFieldMap, WeierstrassCurve.map_preΨ₄]
  rw [functionFieldMap_eval_genX]

@[simp]
theorem functionFieldMap_preΨ_eval (n : ℤ) :
    functionFieldMap W K (((W.map (algebraMap F W.FunctionField)).preΨ n).eval (genX W))
      = (((W.map (algebraMap F K)).map
          (algebraMap K (W.map (algebraMap F K)).FunctionField)).preΨ n).eval
            (genX (W.map (algebraMap F K))) := by
  conv_rhs => rw [← map_map_functionFieldMap, WeierstrassCurve.map_preΨ]
  rw [functionFieldMap_eval_genX]

@[simp]
theorem functionFieldMap_ψ_evalEval (n : ℤ) :
    functionFieldMap W K
        (((W.map (algebraMap F W.FunctionField)).ψ n).evalEval (genX W) (genY W))
      = (((W.map (algebraMap F K)).map
          (algebraMap K (W.map (algebraMap F K)).FunctionField)).ψ n).evalEval
            (genX (W.map (algebraMap F K))) (genY (W.map (algebraMap F K))) := by
  conv_rhs => rw [← map_map_functionFieldMap, WeierstrassCurve.map_ψ]
  rw [functionFieldMap_evalEval_gen]

/-! ## The multiplication-by-`n` endomorphisms -/

theorem functionFieldMap_mulByTwoCoordHom (h2 : (2 : F) ≠ 0) (h2' : (2 : K) ≠ 0)
    (a : W.CoordinateRing) :
    functionFieldMap W K (mulByTwoCoordHom h2 a)
      = mulByTwoCoordHom (W := W.map (algebraMap F K)) h2'
          (CoordinateRing.map W (algebraMap F K) a) := by
  have key : (functionFieldMap W K).comp (mulByTwoCoordHom h2)
      = (mulByTwoCoordHom (W := W.map (algebraMap F K)) h2').comp
          (CoordinateRing.map W (algebraMap F K)) := by
    refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun c => ?_) ?_) ?_
    · simp only [RingHom.comp_apply, mulByTwoCoordHom, CoordinateRing.map, AdjoinRoot.lift_of,
        coe_eval₂RingHom, Polynomial.coe_mapRingHom, Polynomial.map_C, eval₂_C,
        functionFieldMap_algebraMap_base]
    · simp only [RingHom.comp_apply, mulByTwoCoordHom, CoordinateRing.map, AdjoinRoot.lift_of,
        coe_eval₂RingHom, Polynomial.coe_mapRingHom, Polynomial.map_X, eval₂_X, map_div₀,
        functionFieldMap_Φ_eval, functionFieldMap_Ψ₂Sq_eval]
    · simp only [RingHom.comp_apply, mulByTwoCoordHom, CoordinateRing.map, AdjoinRoot.lift_root,
        map_div₀, map_sub, map_mul, map_add, map_pow, map_ofNat, functionFieldMap_map_a₁,
        functionFieldMap_map_a₃, functionFieldMap_Φ_eval, functionFieldMap_Ψ₂Sq_eval,
        functionFieldMap_preΨ₄_eval, functionFieldMap_ψ_evalEval]
  exact RingHom.congr_fun key a

/-- **Base change intertwines the multiplication-by-`2` endomorphism.** -/
theorem functionFieldMap_mulByTwoEndo (h2 : (2 : F) ≠ 0) (h2' : (2 : K) ≠ 0)
    (z : W.FunctionField) :
    functionFieldMap W K (mulByTwoEndo h2 z)
      = mulByTwoEndo (W := W.map (algebraMap F K)) h2' (functionFieldMap W K z) := by
  have key : (functionFieldMap W K).comp (mulByTwoEndo h2)
      = (mulByTwoEndo (W := W.map (algebraMap F K)) h2').comp (functionFieldMap W K) := by
    refine IsFractionRing.ringHom_ext (A := W.CoordinateRing) fun a => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, mulByTwoEndo_algebraMap,
      functionFieldMap_algebraMap, mulByTwoEndo_algebraMap,
      functionFieldMap_mulByTwoCoordHom h2 h2']
  exact RingHom.congr_fun key z

theorem functionFieldMap_mulByThreeCoordHom (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h2' : (2 : K) ≠ 0) (h3' : (3 : K) ≠ 0) (a : W.CoordinateRing) :
    functionFieldMap W K (mulByThreeCoordHom h2 h3 a)
      = mulByThreeCoordHom (W := W.map (algebraMap F K)) h2' h3'
          (CoordinateRing.map W (algebraMap F K) a) := by
  have key : (functionFieldMap W K).comp (mulByThreeCoordHom h2 h3)
      = (mulByThreeCoordHom (W := W.map (algebraMap F K)) h2' h3').comp
          (CoordinateRing.map W (algebraMap F K)) := by
    refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun c => ?_) ?_) ?_
    · simp only [RingHom.comp_apply, mulByThreeCoordHom, CoordinateRing.map, AdjoinRoot.lift_of,
        coe_eval₂RingHom, Polynomial.coe_mapRingHom, Polynomial.map_C, eval₂_C,
        functionFieldMap_algebraMap_base]
    · simp only [RingHom.comp_apply, mulByThreeCoordHom, CoordinateRing.map, AdjoinRoot.lift_of,
        coe_eval₂RingHom, Polynomial.coe_mapRingHom, Polynomial.map_X, eval₂_X, map_div₀,
        functionFieldMap_Φ_eval, functionFieldMap_ΨSq_eval]
    · simp only [RingHom.comp_apply, mulByThreeCoordHom, CoordinateRing.map, AdjoinRoot.lift_root,
        map_div₀, map_sub, map_mul, map_add, map_pow, map_ofNat, functionFieldMap_map_a₁,
        functionFieldMap_map_a₃, functionFieldMap_genX, functionFieldMap_genY,
        functionFieldMap_Φ_eval, functionFieldMap_preΨ_eval, functionFieldMap_preΨ₄_eval,
        functionFieldMap_ψ_evalEval]
  exact RingHom.congr_fun key a

/-- **Base change intertwines the multiplication-by-`3` endomorphism.** -/
theorem functionFieldMap_mulByThreeEndo (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h2' : (2 : K) ≠ 0) (h3' : (3 : K) ≠ 0) (z : W.FunctionField) :
    functionFieldMap W K (mulByThreeEndo h2 h3 z)
      = mulByThreeEndo (W := W.map (algebraMap F K)) h2' h3' (functionFieldMap W K z) := by
  have key : (functionFieldMap W K).comp (mulByThreeEndo h2 h3)
      = (mulByThreeEndo (W := W.map (algebraMap F K)) h2' h3').comp (functionFieldMap W K) := by
    refine IsFractionRing.ringHom_ext (A := W.CoordinateRing) fun a => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, mulByThreeEndo_algebraMap,
      functionFieldMap_algebraMap, mulByThreeEndo_algebraMap,
      functionFieldMap_mulByThreeCoordHom h2 h3 h2' h3']
  exact RingHom.congr_fun key z


/-! ## The translation endomorphism -/

open Classical in
/-- The generic slope of `P + T` transported along the base-change map. -/
private lemma functionFieldMap_slope_gen (x₂ y₂ : F) :
    functionFieldMap W K ((W.map (algebraMap F W.FunctionField)).slope (genX W)
        (algebraMap F W.FunctionField x₂) (genY W) (algebraMap F W.FunctionField y₂))
      = ((W.map (algebraMap F K)).map
            (algebraMap K (W.map (algebraMap F K)).FunctionField)).slope (genX _)
          (algebraMap K (W.map (algebraMap F K)).FunctionField (algebraMap F K x₂)) (genY _)
          (algebraMap K (W.map (algebraMap F K)).FunctionField (algebraMap F K y₂)) := by
  rw [← map_slope (functionFieldMap W K), map_map_functionFieldMap, functionFieldMap_genX,
    functionFieldMap_genY, functionFieldMap_algebraMap_base,
    functionFieldMap_algebraMap_base]

open Classical in
private lemma functionFieldMap_addX_gen (x₂ y₂ : F) :
    functionFieldMap W K ((W.map (algebraMap F W.FunctionField)).addX (genX W)
        (algebraMap F W.FunctionField x₂)
        ((W.map (algebraMap F W.FunctionField)).slope (genX W)
          (algebraMap F W.FunctionField x₂) (genY W) (algebraMap F W.FunctionField y₂)))
      = ((W.map (algebraMap F K)).map
            (algebraMap K (W.map (algebraMap F K)).FunctionField)).addX (genX _)
          (algebraMap K (W.map (algebraMap F K)).FunctionField (algebraMap F K x₂))
          (((W.map (algebraMap F K)).map
            (algebraMap K (W.map (algebraMap F K)).FunctionField)).slope (genX _)
            (algebraMap K (W.map (algebraMap F K)).FunctionField (algebraMap F K x₂)) (genY _)
            (algebraMap K (W.map (algebraMap F K)).FunctionField (algebraMap F K y₂))) := by
  rw [← map_addX (functionFieldMap W K), map_map_functionFieldMap, functionFieldMap_genX,
    functionFieldMap_algebraMap_base, functionFieldMap_slope_gen]

open Classical in
private lemma functionFieldMap_addY_gen (x₂ y₂ : F) :
    functionFieldMap W K ((W.map (algebraMap F W.FunctionField)).addY (genX W)
        (algebraMap F W.FunctionField x₂) (genY W)
        ((W.map (algebraMap F W.FunctionField)).slope (genX W)
          (algebraMap F W.FunctionField x₂) (genY W) (algebraMap F W.FunctionField y₂)))
      = ((W.map (algebraMap F K)).map
            (algebraMap K (W.map (algebraMap F K)).FunctionField)).addY (genX _)
          (algebraMap K (W.map (algebraMap F K)).FunctionField (algebraMap F K x₂)) (genY _)
          (((W.map (algebraMap F K)).map
            (algebraMap K (W.map (algebraMap F K)).FunctionField)).slope (genX _)
            (algebraMap K (W.map (algebraMap F K)).FunctionField (algebraMap F K x₂)) (genY _)
            (algebraMap K (W.map (algebraMap F K)).FunctionField (algebraMap F K y₂))) := by
  rw [← map_addY (functionFieldMap W K), map_map_functionFieldMap, functionFieldMap_genX,
    functionFieldMap_genY, functionFieldMap_algebraMap_base, functionFieldMap_slope_gen]

open Classical in
theorem functionFieldMap_translateCoordHom (h₂ : W.Equation x₂ y₂) (a : W.CoordinateRing) :
    functionFieldMap W K (translateCoordHom h₂ a)
      = translateCoordHom (h₂.map (algebraMap F K))
          (CoordinateRing.map W (algebraMap F K) a) := by
  have key : (functionFieldMap W K).comp (translateCoordHom h₂)
      = (translateCoordHom (h₂.map (algebraMap F K))).comp
          (CoordinateRing.map W (algebraMap F K)) := by
    refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun c => ?_) ?_) ?_
    · simp only [RingHom.comp_apply, translateCoordHom, CoordinateRing.map, AdjoinRoot.lift_of,
        coe_eval₂RingHom, Polynomial.coe_mapRingHom, Polynomial.map_C, eval₂_C,
        functionFieldMap_algebraMap_base]
    · simp only [RingHom.comp_apply, translateCoordHom, CoordinateRing.map, AdjoinRoot.lift_of,
        coe_eval₂RingHom, Polynomial.coe_mapRingHom, Polynomial.map_X, eval₂_X]
      exact functionFieldMap_addX_gen x₂ y₂
    · simp only [RingHom.comp_apply, translateCoordHom, CoordinateRing.map, AdjoinRoot.lift_root]
      exact functionFieldMap_addY_gen x₂ y₂
  exact RingHom.congr_fun key a

variable [W.IsElliptic]

theorem functionFieldMap_translateEndo (h₂ : W.Equation x₂ y₂) (z : W.FunctionField) :
    functionFieldMap W K (translateEndo h₂ z)
      = translateEndo (h₂.map (algebraMap F K)) (functionFieldMap W K z) := by
  have key : (functionFieldMap W K).comp (translateEndo h₂)
      = (translateEndo (h₂.map (algebraMap F K))).comp (functionFieldMap W K) := by
    refine IsFractionRing.ringHom_ext (A := W.CoordinateRing) fun a => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, translateEndo_algebraMap,
      functionFieldMap_algebraMap, translateEndo_algebraMap, functionFieldMap_translateCoordHom]
  exact RingHom.congr_fun key z

end CoordinateRing
end WeierstrassCurve.Affine
