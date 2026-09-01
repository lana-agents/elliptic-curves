/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.MulByTwoFinite
import EllipticCurves.FunctionField.TranslationDoublingComm
import EllipticCurves.FunctionField.WeilPairingBilinearBaseField

/-!
# The general doubling/translation commutation `τ_P∗ ∘ [2]∗ = [2]∗ ∘ τ_T∗` for `[2]P = T`

`EllipticCurves.FunctionField.TranslationDoublingComm` proves the commutation of `translateEndo`
with `mulByTwoEndo` **only** in the degenerate case: for a `2`-torsion `T`,
`translateEndo hT (mulByTwoEndo h2 f) = mulByTwoEndo h2 f`.  Read geometrically that is
`[2](Q + T) = [2]Q`, i.e. `[2]T = O`, and it is the case `P := T` of the identity below with the
right-hand translation collapsing to the identity.

This file proves the **general** form.  For affine points `P` and `T` with `[2]P = T`,

```
[2](Q + P) = [2]Q + T        ⟹        τ_P∗ ([2]∗ f) = [2]∗ (τ_T∗ f).
```

⚠️ **The two translations are on opposite sides and by different points.**  With `τ_P∗ f = f ∘ τ_P`
and `[2]∗ f = f ∘ [2]`,

```
(τ_P∗ ([2]∗ f))(Q) = f(2(Q + P)) = f(2Q + T) = (τ_T∗ f)(2Q) = ([2]∗ (τ_T∗ f))(Q),
```

so it is `translateEndo hP ∘ mulByTwoEndo = mulByTwoEndo ∘ translateEndo hT`.  Writing it the other
way round gives a false statement.

## Main results

* `translateEndo_mulByTwoEndo_comp_general` — the operator identity
  `(translateEndo hP).comp (mulByTwoEndo h2) = (mulByTwoEndo h2).comp (translateEndo hT)`;
* `translateEndo_mulByTwoEndo_apply_general` — its applied form;
* `translateEndo_mulByTwoEndo_apply_of_baseField` — the same, from the **base-field** relation
  `P ⊕ P = T` in `W.Point`, which is the shape a caller actually has.

Supporting API, all of it reusable for `[3]` and for any other `F`-algebra endomorphism of `F(W)`
(`mulByTwoEndoAlgHom`, `[2]∗` as such an endomorphism, lives in `MulByTwoFinite`):

* `algHom_ext_gen` — two `F`-algebra endomorphisms of `F(W)` agreeing on `genX W` and `genY W` are
  equal;
* `genPointHom` — Mathlib's `Point.map` at such an endomorphism, as an `AddMonoidHom` of
  `(W ⁄ F(W)).Point`, with `genPointHom_some`, `genPointHom_comp` and
  `algHom_ext_of_genPointHom`.

## The route: a group calculation, not a generator computation

`TranslationDoublingComm` is ~190 lines, most of it the coordinate work of pushing `translateEndo`
through the doubling formula, with two branch side-conditions (the sum is not `2`-torsion; the
`x`-coordinates differ) discharged by hand.  None of that is needed here, because Mathlib's
`Point.map` is an `AddMonoidHom`: an `F`-algebra endomorphism `φ` of `F(W)` acts on
`(W ⁄ F(W)).Point` *additively*, and it acts on the generic point by applying `φ` to its
coordinates.  So, writing `𝒫` for the generic point, `𝒫_P`/`𝒯` for the constant points:

```
genPointHom τ_P (genPointHom [2] 𝒫) = genPointHom τ_P (𝒫 + 𝒫)
                                    = (𝒫 + 𝒫_P) + (𝒫 + 𝒫_P)
                                    = (𝒫 + 𝒫) + (𝒫_P + 𝒫_P)      -- add_add_add_comm
                                    = (𝒫 + 𝒫) + 𝒯                -- the hypothesis [2]P = T
                                    = genPointHom [2] 𝒫 + genPointHom [2] 𝒯
                                    = genPointHom [2] (𝒫 + 𝒯)
                                    = genPointHom [2] (genPointHom τ_T 𝒫)
```

using only that constants are fixed by `[2]` (`AlgHom.commutes`) and the two merged correspondences
`genericPoint_add_self` (`[2]` acts as `𝒫 ↦ 𝒫 + 𝒫`) and `genericPoint_add_translatePoint` (`τ_T`
acts as `𝒫 ↦ 𝒫 + 𝒯`).  Reading off coordinates (`Point.some.injEq`) gives the two generator
identities, and `algHom_ext_gen` upgrades them to the operator identity.  **No branch condition
occurs**: the tangent/secant case split was already done, once, inside those two merged
correspondences.

## Hypothesis shape

The statement takes the `F(W)`-level relation `translatePoint hP + translatePoint hP =
translatePoint hT`, matching `TranslationDoublingComm`'s `htors`, and the base-field bridge is a
separate corollary through the merged `translatePoint_add`.  That is what keeps it reusable: the
`[3]` analogue will want the same `F(W)`-level input.

## What is *not* here

* The `n = 2` alternating property itself — that is `#688`, which consumes this.
* `#418`, the Weil pairing, `[3]`, Ward.
* Any generalisation of `translateEndo` to a non-rational or possibly-zero translation point
  (`#679`, `#689`): both `P` and `T` here are affine `F`-points, given by `W.Equation`.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.
-/

open Polynomial

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} {xP yP xT yT : F}

/-! ### `F`-algebra endomorphisms of `F(W)` and their action on points -/

/-- **Generator extensionality for `F`-algebra endomorphisms of `F(W)`.**  Two of them agreeing on
the coordinate generators `genX W` and `genY W` are equal.

`F(W)` is the fraction field of `F[W] = AdjoinRoot W.polynomial` (`IsFractionRing.ringHom_ext`), and
a ring homomorphism out of `AdjoinRoot W.polynomial` is determined by its values on the constants
and on the two generators `mk W (C X)` and `AdjoinRoot.root W.polynomial`
(`AdjoinRoot.ringHom_ext` + `Polynomial.ringHom_ext`) — whose images in `F(W)` are `genX W` and
`genY W` by definition.  On the constants there is nothing to check: both maps are `F`-algebra
homomorphisms. -/
theorem algHom_ext_gen {φ ψ : W.FunctionField →ₐ[F] W.FunctionField}
    (hx : φ (genX W) = ψ (genX W)) (hy : φ (genY W) = ψ (genY W)) : φ = ψ := by
  have hcr : (φ : W.FunctionField →+* W.FunctionField).comp (genPsi W)
      = (ψ : W.FunctionField →+* W.FunctionField).comp (genPsi W) := by
    refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun c => ?_) ?_) ?_
    · have hofC : AdjoinRoot.of W.polynomial (C c) = algebraMap F W.CoordinateRing c := by
        rw [IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing, AdjoinRoot.algebraMap_eq,
          ← Polynomial.C_eq_algebraMap]
      simp only [RingHom.comp_apply, hofC, genPsi, ← IsScalarTower.algebraMap_apply,
        AlgHom.coe_toRingHom, AlgHom.commutes]
    · have hx' : φ (genPsi W (mk W (C X))) = ψ (genPsi W (mk W (C X))) := hx
      simpa only [RingHom.comp_apply, show AdjoinRoot.of W.polynomial X = mk W (C X) from rfl,
        AlgHom.coe_toRingHom] using hx'
    · have hy' : φ (genPsi W (AdjoinRoot.root W.polynomial))
          = ψ (genPsi W (AdjoinRoot.root W.polynomial)) := hy
      simpa only [RingHom.comp_apply, AlgHom.coe_toRingHom] using hy'
  refine AlgHom.coe_ringHom_injective ?_
  refine IsFractionRing.ringHom_ext (A := W.CoordinateRing) (fun a => ?_)
  exact congr($hcr a)

/-- Base-changing `W ⁄ F(W)` again along an `F`-algebra endomorphism of `F(W)` returns the same
curve, because such an endomorphism fixes `algebraMap F F(W)`.  (The `translateEndo` case of this is
private in `TranslationComposition`.) -/
private lemma map_algHom_curve (φ : W.FunctionField →ₐ[F] W.FunctionField) :
    (W.map (algebraMap F W.FunctionField)).map (φ : W.FunctionField →+* W.FunctionField)
      = W.map (algebraMap F W.FunctionField) := by
  have hcomp : (φ : W.FunctionField →+* W.FunctionField).comp (algebraMap F W.FunctionField)
      = algebraMap F W.FunctionField := RingHom.ext φ.commutes
  simp only [WeierstrassCurve.map_map, hcomp]

/-- An `F`-algebra endomorphism of `F(W)` carries points of `W ⁄ F(W)` to points of `W ⁄ F(W)`. -/
lemma nonsingular_algHom (φ : W.FunctionField →ₐ[F] W.FunctionField) {x y : W.FunctionField}
    (h : (W.map (algebraMap F W.FunctionField)).Nonsingular x y) :
    (W.map (algebraMap F W.FunctionField)).Nonsingular (φ x) (φ y) := by
  have key := ((W.map (algebraMap F W.FunctionField)).map_nonsingular
    (f := (φ : W.FunctionField →+* W.FunctionField))
    (φ : W.FunctionField →+* W.FunctionField).injective x y).mpr h
  rwa [map_algHom_curve φ] at key

/-- **The action of an `F`-algebra endomorphism of `F(W)` on `(W ⁄ F(W)).Point`**, as an
`AddMonoidHom`: Mathlib's `WeierstrassCurve.Affine.Point.map`, specialised to source and target
field both `F(W)`.  Being additive is the whole content of this file's route. -/
noncomputable def genPointHom (φ : W.FunctionField →ₐ[F] W.FunctionField) :
    (W.map (algebraMap F W.FunctionField)).Point →+
      (W.map (algebraMap F W.FunctionField)).Point :=
  Point.map (W' := W) φ

/-- `genPointHom` acts on an affine point by applying `φ` to both coordinates. -/
lemma genPointHom_some (φ : W.FunctionField →ₐ[F] W.FunctionField) {x y : W.FunctionField}
    (h : (W.map (algebraMap F W.FunctionField)).Nonsingular x y) :
    genPointHom φ (Point.some x y h) = Point.some (φ x) (φ y) (nonsingular_algHom φ h) :=
  rfl

/-- `genPointHom` is functorial.  Note the order: `genPointHom φ ∘ genPointHom ψ` is the action of
the *composite ring homomorphism* `φ ∘ ψ`, which as a map of points is "first `φ`'s point, then
`ψ`'s" — the contravariance that makes `τ_P∗ ∘ [2]∗` correspond to `Q ↦ 2(Q + P)`. -/
lemma genPointHom_comp (φ ψ : W.FunctionField →ₐ[F] W.FunctionField)
    (P : (W.map (algebraMap F W.FunctionField)).Point) :
    genPointHom φ (genPointHom ψ P) = genPointHom (φ.comp ψ) P :=
  Point.map_map _ _ P

variable [W.IsElliptic]

/-- **Extensionality through the generic point.**  Two `F`-algebra endomorphisms of `F(W)` agreeing
on `𝒫` agree, since the coordinates of `genPointHom φ 𝒫` are `φ (genX W)` and `φ (genY W)`. -/
theorem algHom_ext_of_genPointHom {φ ψ : W.FunctionField →ₐ[F] W.FunctionField}
    (h : genPointHom φ genericPoint = genPointHom ψ genericPoint) : φ = ψ := by
  rw [genericPoint, genPointHom_some, genPointHom_some, Point.some.injEq] at h
  exact algHom_ext_gen h.1 h.2

/-- `[2]∗` acts on the generic point as the group double — the merged `genericPoint_add_self`, read
through `genPointHom`. -/
lemma genPointHom_genericPoint_mulByTwo (h2 : (2 : F) ≠ 0) :
    genPointHom (mulByTwoEndoAlgHom (W := W) h2) genericPoint = genericPoint + genericPoint :=
  (genericPoint_add_self h2).symm

/-- `τ_T∗` acts on the generic point as `+ 𝒯` — the merged `genericPoint_add_translatePoint`, read
through `genPointHom`. -/
lemma genPointHom_genericPoint_translate (h₂ : W.Equation xP yP) :
    genPointHom (translateEndoAlgHom h₂) genericPoint = genericPoint + translatePoint h₂ :=
  (genericPoint_add_translatePoint h₂).symm

/-- Every `F`-algebra endomorphism of `F(W)` fixes the constant points. -/
lemma genPointHom_translatePoint (φ : W.FunctionField →ₐ[F] W.FunctionField)
    (h₂ : W.Equation xT yT) :
    genPointHom φ (translatePoint h₂) = translatePoint h₂ := by
  rw [translatePoint, genPointHom_some, Point.some.injEq]
  exact ⟨φ.commutes xT, φ.commutes yT⟩

/-! ### The commutation -/

/-- **The commutation, as `F`-algebra endomorphisms.**  For affine points `P`, `T` with `[2]P = T`
in `(W ⁄ F(W)).Point`,

```
τ_P∗ ∘ [2]∗ = [2]∗ ∘ τ_T∗.
```

The proof is the group calculation `(𝒫 + 𝒫_P) + (𝒫 + 𝒫_P) = (𝒫 + 𝒫) + (𝒫_P + 𝒫_P) = (𝒫 + 𝒫) + 𝒯`
transported through `genPointHom`; see the module docstring. -/
theorem translateEndoAlgHom_comp_mulByTwoEndoAlgHom (hP : W.Equation xP yP)
    (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0)
    (hdouble : translatePoint hP + translatePoint hP = translatePoint hT) :
    (translateEndoAlgHom hP).comp (mulByTwoEndoAlgHom h2)
      = (mulByTwoEndoAlgHom h2).comp (translateEndoAlgHom hT) := by
  refine algHom_ext_of_genPointHom ?_
  simp only [← genPointHom_comp, genPointHom_genericPoint_mulByTwo,
    genPointHom_genericPoint_translate, map_add, genPointHom_translatePoint]
  rw [add_add_add_comm, hdouble]

/-- **The commutation, as ring homomorphisms.**  `(translateEndo hP).comp (mulByTwoEndo h2)
= (mulByTwoEndo h2).comp (translateEndo hT)` whenever `[2]P = T`.

The merged `translateEndo_mulByTwoEndo_comp` is *not* this statement: it is the degenerate case
`P := T` with `[2]T = O`, where the right-hand side collapses to `mulByTwoEndo h2`. -/
theorem translateEndo_mulByTwoEndo_comp_general (hP : W.Equation xP yP)
    (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0)
    (hdouble : translatePoint hP + translatePoint hP = translatePoint hT) :
    (translateEndo hP).comp (mulByTwoEndo h2)
      = (mulByTwoEndo h2).comp (translateEndo hT) :=
  congrArg AlgHom.toRingHom (translateEndoAlgHom_comp_mulByTwoEndoAlgHom hP hT h2 hdouble)

/-- **The commutation in applied form.**  For every `f : F(W)`,
`τ_P∗ ([2]∗ f) = [2]∗ (τ_T∗ f)` when `[2]P = T`. -/
theorem translateEndo_mulByTwoEndo_apply_general (hP : W.Equation xP yP)
    (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0)
    (hdouble : translatePoint hP + translatePoint hP = translatePoint hT)
    (f : W.FunctionField) :
    translateEndo hP (mulByTwoEndo h2 f) = mulByTwoEndo h2 (translateEndo hT f) := by
  have h := translateEndo_mulByTwoEndo_comp_general hP hT h2 hdouble
  exact congr($h f)

open Classical in
/-- **The commutation from a base-field relation.**  The hypothesis a caller actually has is
`P ⊕ P = T` in `W.Point`; the merged `translatePoint_add` transports it to the `F(W)`-level
relation the theorem above consumes. -/
theorem translateEndo_mulByTwoEndo_apply_of_baseField (hP : W.Equation xP yP)
    (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0)
    (hdouble : torsionPoint hP + torsionPoint hP = torsionPoint hT) (f : W.FunctionField) :
    translateEndo hP (mulByTwoEndo h2 f) = mulByTwoEndo h2 (translateEndo hT f) :=
  translateEndo_mulByTwoEndo_apply_general hP hT h2 (translatePoint_add hP hP hT hdouble) f

/-! ### Non-vacuity

The hypothesis `[2]P = T` with **both** `P` and `T` affine is genuinely restrictive: on a curve
whose only rational points are `O` and the `2`-torsion (`y² = x³ - x` over `ℚ`, the curve the rest
of this subtree uses for its certificates) every affine `P` doubles to `O`, and the theorems above
would be vacuous.  So the certificate here is on `y² = x³ + 1`, where `P = (2, 3)` doubles to
`T = (0, 1)`. -/

section Nonvacuity

/-! The certificate curve `y² = x³ + 1` is the shared `EllipticCurves.Fixture.y2EqX3AddOne`, whose
single `[CharZero F]` instance also supplies `IsElliptic` here. -/

open EllipticCurves.Fixture

/-- `P = (2, 3)` lies on `y² = x³ + 1`. -/
private lemma exampleEquationP : (y2EqX3AddOne ℚ).Equation 2 3 := by
  norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff]

/-- `T = (0, 1)` lies on `y² = x³ + 1`. -/
private lemma exampleEquationT : (y2EqX3AddOne ℚ).Equation 0 1 := by
  norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff]

open Classical in
/-- `[2](2, 3) = (0, 1)`: the tangent at `P` has slope `2`, so `x(2P) = 4 - 4 = 0`. -/
private lemma exampleDouble :
    torsionPoint exampleEquationP + torsionPoint exampleEquationP
      = torsionPoint exampleEquationT := by
  have hy : (3 : ℚ) ≠ (y2EqX3AddOne ℚ).negY 2 3 := by
    norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.negY]
  have key : Point.some (2 : ℚ) 3 ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEquationP)
        + Point.some (2 : ℚ) 3 ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEquationP)
      = Point.some (0 : ℚ) 1 ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEquationT) := by
    rw [Point.add_self_of_Y_ne hy, Point.some.injEq]
    constructor <;>
      norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
        WeierstrassCurve.Affine.slope]
  exact key

-- The `convert` is bookkeeping, not mathematics: `translateEndo_mulByTwoEndo_apply_of_baseField`
-- is stated `open Classical in`, so the `+` in its hypothesis carries `Classical.propDecidable`,
-- while `exampleDouble` — elaborated at `F = ℚ`, where a `DecidableEq` instance exists — carries
-- `instDecidableEqRat`.  `convert ... using 4` closes the gap by `Subsingleton.elim` on the two
-- `DecidableEq ℚ` instances.
open Classical in
example (f : (y2EqX3AddOne ℚ).FunctionField) :
    translateEndo exampleEquationP (mulByTwoEndo (W := y2EqX3AddOne ℚ) (by norm_num) f)
      = mulByTwoEndo (by norm_num) (translateEndo exampleEquationT f) :=
  translateEndo_mulByTwoEndo_apply_of_baseField exampleEquationP exampleEquationT
    (by norm_num) (by convert exampleDouble using 4) f

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
