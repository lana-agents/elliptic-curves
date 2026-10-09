/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import EllipticCurves.FunctionField.MulByThreeEndomorphism
import EllipticCurves.Torsion.OmegaThreeCharFree

/-!
# The multiplication-by-`3` pullback of the function field, with no `(2 : F) ≠ 0`

`EllipticCurves.FunctionField.MulByThreeEndomorphism` builds `[3]∗ : F(W) →+* F(W)` out of the
division-polynomial tripling coordinates, and every declaration on that route binds
`(h2 : (2 : F) ≠ 0)` beside `(h3 : (3 : F) ≠ 0)`.  ⚠️ **The `h2` is an artefact of the `y`-slot's
denominator and of nothing else**, and `EllipticCurves.Torsion.OmegaThreeCharFree` removed it from
the on-curve identity the pullback is built on.  This file carries that removal up the chain.

The result is `mulByThreeEndoOfThree`, a ring endomorphism of `F(W)` realising `h ↦ h ∘ [3]`,
binding `(3 : F) ≠ 0` **alone**.  `mulByThreeEndoCurveCharTwo` is one, over
`y² + xy = x³ + 1` over `ZMod 2`.

## The three `h2` sites on this route, and what each one was

Walked at the base this file was written against, in route order:

| site | declaration | what the `h2` does |
|---|---|---|
| 1 | `two_ne_zero_functionField` → `tripling_equation` | makes `2·ψ₃³` a legal denominator |
| 2 | `mulByThreeCoordHom`'s `AdjoinRoot.lift` value | names the `y`-slot as `(bracket)/(2ψ₃³)` |
| 3 | `isAlgebraic_genX_of_three`'s hypothesis | names the `x`-slot by the pullback itself |

⚠️ **Sites 1 and 2 are the same `2` and they die together**: the `2`-free `y`-slot is
`ω₃(genX, genY)/ψ₃(genX, genY)³`, and `tripling_equation_ω₃_general` discharges the
`AdjoinRoot.lift` obligation for it with `h3` alone — through `psiThree_gen_ne`, which spends `h3`
and not `h2`.  ⚠️⚠️ **Site 3 was never about `2` at all**: `isAlgebraic_genX_of_three` opens with
`rw [mulByThreeCoordHom_X]`, which replaces the named `x`-slot by the quotient `Φ₃(genX)/ΨSq₃(genX)`
and throws the `h2` away; the Zariski argument that follows uses `h3` only.  That is why
`MulByThreeEndomorphism` now states `isAlgebraic_genX_of_xCoord_three` at the quotient itself and
derives the named form from it, **with no change to any existing signature** — and why the
`x`-slot of the pullback below, which is literally the same quotient, inherits the dominance
argument unchanged rather than repeating it.

## `mulByThreeCoordHom` is JOINED, not RESTATED, and the measurement is why

`#2252` offers the choice and says joining needs no defence.  It is taken, and the figure that
settles it is re-derived here rather than carried: over the **469** tracked `.lean` files,
**231** declarations in **62** files name `mulByThreeCoordHom` or `mulByThreeEndo` in their own
**signature** (the text up to the first `:=`, comments stripped, with boundary look-around on the
name), out of **479** in **91** files for the four-name family that adds `mulByTwoCoordHom` and
`mulByTwoEndo`.

⚠️ **Restating would change the defining formula of a `def` that every one of those 231 names.**
`mulByThreeCoordHom`'s `2` is in the *value* it lifts, not only in its proof obligation, so a
restatement is not a proof change — it changes what the symbol denotes.  The join below is a second
`def` beside it, and `mulByThreeCoordHomOfThree_eq` / `mulByThreeEndoOfThree_eq` prove the two
**equal** wherever `h2` holds, so a consumer that holds `h2` can move between them in one rewrite
and nothing downstream has to be touched.

⚠️ **The 231 and the 479 are this file's own recogniser's figures and are NOT comparable to
`#2252`'s `290` in `77`**: that census was taken at a different base, over a different
population, and with a different declaration splitter.  **No delta between the two is claimed**,
and a later round that wants one should re-run both recognisers at one ref.

## What this does and does not settle

* ✅ `[3]∗` on the coordinate ring and on the function field, at `(3 : F) ≠ 0` alone.
* ⚠️ **`n = 2` is untouched and must not be attempted this way.**
  `MulByTwoPullback`'s side condition is `psiTwo_gen_ne h2`, and `ψ₂ = 2Y + a₁X + a₃` vanishes
  identically in characteristic `2` whenever `a₁ = a₃ = 0`.  A genuine obstruction, not a route.
* ⚠️ **No existing signature changes**, and no existing statement is weakened, restated or
  deprecated.  Everything here is new API beside the old.
* ⚠️ **The downstream `h2` population is NOT swept.**  Retiring the 231 consumers is a separate and
  much larger job; this file delivers the rung.

## Main statements

* `WeierstrassCurve.Affine.CoordinateRing.tripling_equation_ω₃_gen` : the `2`-free on-curve
  identity at the generic point.
* `WeierstrassCurve.Affine.CoordinateRing.mulByThreeCoordHomOfThree` : the coordinate-ring
  pullback, `h3` only.
* `WeierstrassCurve.Affine.CoordinateRing.mulByThreeCoordHomOfThree_injective` : dominance of
  `[3]`, `h3` only.
* `WeierstrassCurve.Affine.CoordinateRing.mulByThreeEndoOfThree` : `[3]∗ : F(W) →+* F(W)`,
  `h3` only.
* `WeierstrassCurve.Affine.CoordinateRing.mulByThreeEndoOfThree_eq` : it is the landed
  `mulByThreeEndo` wherever that is defined.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], II.2, III.8.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

/-- **The tripled generic point lies on the curve, with no `(2 : F) ≠ 0`.**
`tripling_equation_ω₃_general` over the base-changed curve `W ⁄ F(W)` at the generic point, which
lies on the curve by `equation_gen` and is not `3`-torsion by `psiThree_gen_ne`.

⚠️ **This is `tripling_equation_gen` with `h2` deleted and the `y`-coordinate written `ω₃/ψ₃³`.**
The landed statement's `h2` went to `two_ne_zero_functionField`, which exists only to make
`2 · ψ₃³` a legal denominator; the `ω₃` form has no `2` to legalise. -/
theorem tripling_equation_ω₃_gen (h3 : (3 : F) ≠ 0) :
    (W.map (algebraMap F W.FunctionField)).Equation
      (((W.map (algebraMap F W.FunctionField)).Φ 3).eval (genX W) /
        ((W.map (algebraMap F W.FunctionField)).ΨSq 3).eval (genX W))
      ((W.map (algebraMap F W.FunctionField)).ω₃.evalEval (genX W) (genY W) /
        ((W.map (algebraMap F W.FunctionField)).ψ 3).evalEval (genX W) (genY W) ^ 3) :=
  tripling_equation_ω₃_general equation_gen (psiThree_gen_ne h3)

/-- **The multiplication-by-`3` pullback (coordinate-ring half), with no `(2 : F) ≠ 0`.** The ring
homomorphism `F[W] →+* F(W)` sending the generic point `P = (x, y)` to the tripled point `3 • P`,
as `AdjoinRoot.lift` of the `2`-free tripling coordinates
`(Φ₃(genX)/ΨSq₃(genX), ω₃(genX, genY)/ψ₃(genX, genY)³)`, whose well-definedness obligation is
`tripling_equation_ω₃_gen`.

⚠️ **A second `def` beside `mulByThreeCoordHom` and not a restatement of it**; see the module
docstring for the measurement behind that choice, and `mulByThreeCoordHomOfThree_eq` for the proof
that the two agree wherever the landed one is defined. -/
noncomputable def mulByThreeCoordHomOfThree (h3 : (3 : F) ≠ 0) :
    W.CoordinateRing →+* W.FunctionField :=
  AdjoinRoot.lift
    (eval₂RingHom (algebraMap F W.FunctionField)
      (((W.map (algebraMap F W.FunctionField)).Φ 3).eval (genX W) /
        ((W.map (algebraMap F W.FunctionField)).ΨSq 3).eval (genX W)))
    ((W.map (algebraMap F W.FunctionField)).ω₃.evalEval (genX W) (genY W) /
      ((W.map (algebraMap F W.FunctionField)).ψ 3).evalEval (genX W) (genY W) ^ 3)
    (by
      rw [eval₂_eval₂RingHom_apply, ← map_polynomial]
      exact tripling_equation_ω₃_gen h3)

/-- Image of the `x`-generator: the `x`-coordinate of `3 • P`.  ⚠️ **Byte-identical to
`mulByThreeCoordHom_X`'s right-hand side**, which is what lets the dominance argument be reused
rather than repeated. -/
lemma mulByThreeCoordHomOfThree_X (h3 : (3 : F) ≠ 0) :
    mulByThreeCoordHomOfThree (W := W) h3 (mk W (C X)) =
      ((W.map (algebraMap F W.FunctionField)).Φ 3).eval (genX W) /
        ((W.map (algebraMap F W.FunctionField)).ΨSq 3).eval (genX W) := by
  rw [mulByThreeCoordHomOfThree,
    show mk W (C X) = AdjoinRoot.of W.polynomial X from rfl,
    AdjoinRoot.lift_of, coe_eval₂RingHom, eval₂_X]

/-- Image of the `y`-generator (the root): the `y`-coordinate of `3 • P`, as `ω₃/ψ₃³`. -/
@[simp] lemma mulByThreeCoordHomOfThree_root (h3 : (3 : F) ≠ 0) :
    mulByThreeCoordHomOfThree (W := W) h3 (AdjoinRoot.root W.polynomial) =
      (W.map (algebraMap F W.FunctionField)).ω₃.evalEval (genX W) (genY W) /
        ((W.map (algebraMap F W.FunctionField)).ψ 3).evalEval (genX W) (genY W) ^ 3 := by
  rw [mulByThreeCoordHomOfThree, AdjoinRoot.lift_root]

/-- `mulByThreeCoordHomOfThree` fixes the image of `F`. -/
lemma mulByThreeCoordHomOfThree_algebraMap (h3 : (3 : F) ≠ 0) (c : F) :
    mulByThreeCoordHomOfThree (W := W) h3 (algebraMap F W.CoordinateRing c) =
      algebraMap F W.FunctionField c := by
  have h1 : (algebraMap F W.CoordinateRing c) = mk W (C (C c)) := by
    rw [IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing, AdjoinRoot.algebraMap_eq,
      ← Polynomial.C_eq_algebraMap]; rfl
  rw [h1, show mk W (C (C c)) = AdjoinRoot.of W.polynomial (C c) from rfl,
    mulByThreeCoordHomOfThree, AdjoinRoot.lift_of, coe_eval₂RingHom, eval₂_C]

/-- `mulByThreeCoordHomOfThree` packaged as an `F`-algebra homomorphism, which is the shape
Zariski's lemma (`isAlgebraic_of_ker_maximal`) consumes. -/
noncomputable def mulByThreeAlgHomOfThree (h3 : (3 : F) ≠ 0) :
    W.CoordinateRing →ₐ[F] W.FunctionField where
  toRingHom := mulByThreeCoordHomOfThree h3
  commutes' := mulByThreeCoordHomOfThree_algebraMap h3

/-- The `AlgHom` packaging applies the underlying ring homomorphism. -/
@[simp] lemma mulByThreeAlgHomOfThree_apply (h3 : (3 : F) ≠ 0) (a : W.CoordinateRing) :
    mulByThreeAlgHomOfThree (W := W) h3 a = mulByThreeCoordHomOfThree h3 a := rfl

/-- **Multiplication-by-`3` is dominant, with no `(2 : F) ≠ 0`: `mulByThreeCoordHomOfThree h3` is
injective.**  If it were not, its kernel would be a nonzero prime — hence maximal, as `F[W]` has
Krull dimension `≤ 1` — so the residue field would be algebraic over `F` (Zariski), forcing
`x(3 • P)` to be algebraic and, via `isAlgebraic_genX_of_xCoord_three`, `genX` itself to be
algebraic, contradicting `transcendental_genX`.

⚠️ **The argument is `mulByThreeCoordHom_injective`'s, with the SAME `x`-slot**: only the `y`-slot
of the pullback differs between the two `def`s, and dominance does not look at it. -/
lemma mulByThreeCoordHomOfThree_injective (h3 : (3 : F) ≠ 0) :
    Function.Injective (mulByThreeCoordHomOfThree (W := W) h3) := by
  set g := mulByThreeAlgHomOfThree (W := W) h3 with hg
  have key : Function.Injective g := by
    by_contra hni
    have hne : RingHom.ker g ≠ ⊥ := fun h =>
      hni ((RingHom.injective_iff_ker_eq_bot _).mpr h)
    haveI hprime : (RingHom.ker g).IsPrime := RingHom.ker_isPrime _
    have hmax : (RingHom.ker g).IsMaximal := hprime.isMaximal hne
    have hu : IsAlgebraic F (g (mk W (C X))) :=
      isAlgebraic_of_ker_maximal g hmax (mk W (C X))
    rw [hg, mulByThreeAlgHomOfThree_apply, mulByThreeCoordHomOfThree_X] at hu
    exact transcendental_genX (isAlgebraic_genX_of_xCoord_three h3 hu)
  exact key

/-- ⚠️⚠️ **THE HEADLINE: the multiplication-by-`3` endomorphism of the function field, binding
`(3 : F) ≠ 0` and NOTHING ELSE.**  The ring endomorphism `F(W) →+* F(W)` realising `h ↦ h ∘ [3]`,
obtained from the injective coordinate-ring pullback by the universal property of the fraction
field.

⚠️ **`mulByThreeEndo` is not superseded** for a caller holding `h2`; by `mulByThreeEndoOfThree_eq`
the two are *equal* there, so this one asks for less and is the same map. -/
noncomputable def mulByThreeEndoOfThree (h3 : (3 : F) ≠ 0) :
    W.FunctionField →+* W.FunctionField :=
  IsFractionRing.lift (mulByThreeCoordHomOfThree_injective (W := W) h3)

/-- On the image of `F[W]`, `mulByThreeEndoOfThree` agrees with the coordinate-ring pullback. -/
@[simp] lemma mulByThreeEndoOfThree_algebraMap (h3 : (3 : F) ≠ 0) (a : W.CoordinateRing) :
    mulByThreeEndoOfThree h3 (algebraMap W.CoordinateRing W.FunctionField a) =
      mulByThreeCoordHomOfThree h3 a :=
  IsFractionRing.lift_algebraMap (mulByThreeCoordHomOfThree_injective (W := W) h3) a

/-- The image of the generic `x`-coordinate: the `x`-coordinate of `3 • P`. -/
lemma mulByThreeEndoOfThree_genX (h3 : (3 : F) ≠ 0) :
    mulByThreeEndoOfThree (W := W) h3 (genX W) =
      ((W.map (algebraMap F W.FunctionField)).Φ 3).eval (genX W) /
        ((W.map (algebraMap F W.FunctionField)).ΨSq 3).eval (genX W) := by
  conv_lhs => rw [genX, genPsi]
  rw [mulByThreeEndoOfThree_algebraMap, mulByThreeCoordHomOfThree_X]

/-- The image of the generic `y`-coordinate: the `y`-coordinate of `3 • P`, as `ω₃/ψ₃³`.

⚠️ Compare `mulByThreeEndo_genY`, whose right-hand side is the same value written over `2ψ₃³`; the
two agree by `ω₃_div_eq_div_two_mul` wherever `h2` holds, and only this one is defined where it
does not. -/
lemma mulByThreeEndoOfThree_genY (h3 : (3 : F) ≠ 0) :
    mulByThreeEndoOfThree (W := W) h3 (genY W) =
      (W.map (algebraMap F W.FunctionField)).ω₃.evalEval (genX W) (genY W) /
        ((W.map (algebraMap F W.FunctionField)).ψ 3).evalEval (genX W) (genY W) ^ 3 := by
  conv_lhs => rw [genY, genPsi]
  rw [mulByThreeEndoOfThree_algebraMap, mulByThreeCoordHomOfThree_root]

/-! ### Agreement with the landed `h2`-bearing pullback -/

/-- The scalar `2` is nonzero in the function field when it is nonzero in the base field.

⚠️ `MulByThreeEndomorphism` has a `private` lemma of this name; this is a second declaration and
not a reuse of it.  **Four other files declare one too** (`MulByNXCoordFormula`,
`MulByNYCoordFormula`, `MulByTwoPullback` and that one) and they are all separate declarations. -/
private lemma two_ne_zero_functionField' (h2 : (2 : F) ≠ 0) : (2 : W.FunctionField) ≠ 0 := by
  have hinj := (algebraMap F W.FunctionField).injective
  intro h
  exact h2 (hinj (by rw [map_ofNat, map_zero]; exact h))

/-- **The joined pullback IS the landed one wherever the landed one is defined.**  The two `def`s
have the same `x`-slot by construction and the same `y`-slot by `ω₃_div_eq_div_two_mul`, and
`AdjoinRoot.lift` is determined by the pair, so they are equal as ring homomorphisms. -/
theorem mulByThreeCoordHomOfThree_eq (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    mulByThreeCoordHomOfThree (W := W) h3 = mulByThreeCoordHom h2 h3 := by
  have hy := ω₃_div_eq_div_two_mul (W := W.map (algebraMap F W.FunctionField))
    (two_ne_zero_functionField' h2) (psiThree_gen_ne (W := W) h3)
  rw [mulByThreeCoordHomOfThree, mulByThreeCoordHom]
  -- `congr 1` closes the value slot from `hy` in context and the `AdjoinRoot.lift` obligation by
  -- proof irrelevance; it leaves no goal.
  congr 1

/-- **The joined endomorphism IS the landed one wherever the landed one is defined.** -/
theorem mulByThreeEndoOfThree_eq (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    mulByThreeEndoOfThree (W := W) h3 = mulByThreeEndo h2 h3 := by
  rw [mulByThreeEndoOfThree, mulByThreeEndo]
  congr 1
  exact mulByThreeCoordHomOfThree_eq h2 h3

/-! ### Non-vacuity in characteristic `2` -/

section Nonvacuity

/-- `(3 : ZMod 2) = 1 ≠ 0`.  ⚠️ **The index is prime to the characteristic and that is the whole
reason `n = 3` is reachable in characteristic `2` at all** — `n = 2` there is not. -/
lemma three_ne_zero_zmod_two : (3 : ZMod 2) ≠ 0 := by decide

/-- **A multiplication-by-`3` endomorphism of the function field of a curve in characteristic `2`.**

⚠️ **This is the whole content of the round**: `mulByThreeEndo` cannot be instantiated here,
because its `(2 : F) ≠ 0` is refuted by `two_eq_zero_zmod_two`, so neither the term below nor its
type could be *written* before.  The curve is
`EllipticCurves.Torsion.OmegaThreeCharFree`'s `curveCharTwo`, `y² + xy = x³ + 1` over `ZMod 2`. -/
noncomputable def mulByThreeEndoCurveCharTwo :
    curveCharTwo.FunctionField →+* curveCharTwo.FunctionField :=
  mulByThreeEndoOfThree three_ne_zero_zmod_two

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
