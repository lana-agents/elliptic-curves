/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.GenericTripling

/-!
# The multiplication-by-`n` pullback `[n]∗ : F(W) → F(W)`, built from the group law

Let `W` be an elliptic curve over a field `F`.  The generic point `𝒫 = (genX W, genY W)` is an
element of the Mathlib group `(W ⁄ F(W)).Point` (`genericPoint`, `GenericPoint.lean`), so `n • 𝒫`
is available for every `n : ℕ` **from the group law alone**.  This file turns an arbitrary affine
point of `W ⁄ F(W)` into an `F`-algebra endomorphism of `F(W)`, and specialises the construction to
`n • 𝒫` to obtain `[n]∗`.

## ⚠️ Why this does not need the `ωₙ` on-curve identity

`#403`/`#405` build `[n]∗` as `AdjoinRoot.lift` of the *division-polynomial* coordinates
`(Φₙ/ΨSqₙ, ωₙ/ψₙ³)`, whose well-definedness obligation `W.polynomial.eval₂ _ _ = 0` is the general
`n` on-curve identity — `#404`'s crux.  ⚠️ That crux is **closed** (see the next section), and both
of the gates the sentence here used to name behind it are closed too: Ward's theorem (`#260`) is
`WeierstrassCurve.Affine.ψ_isEllipticNet` of `EllipticCurves.Torsion.WardHalving`, unconditional
and on the current pin.

**Taking the coordinates from `n • 𝒫` discharges that obligation for free**: `n • 𝒫` is a
`Point`, and a `Point` carries its own `Nonsingular` field, whose first component *is* the
Weierstrass equation.  Nothing about division polynomials, elliptic nets or the four-term recurrence
enters this file.  What the general `n` construction needs instead is that `x(n • 𝒫)` is
**transcendental** over `F` — geometrically, that `[n]` is non-constant — and that is a hypothesis
here, discharged in `EllipticCurves.FunctionField.MulByNTranscendence`.

⚠️ The two merged low-index endomorphisms are *recovered*, not re-proved: `mulByNEndo_two` and
`mulByNEndo_three` identify this construction at `n = 2, 3` with `mulByTwoEndo` and
`mulByThreeEndo`, which were built from `doubling_equation`/`tripling_equation`.  That agreement is
the validation of the route.

## ⚠️ `#404` is CLOSED, and this tree used its number for two different propositions

⚠️ **Check this section before citing `#404` as a gate.**  `#1460` found **75** sites across **55**
files still naming it as open, and they do not all mean the same statement.

* ✅ **The on-curve identity** — `#404`'s stated deliverable, and **closed** by PR #557.  It says
  the point `(Φₙ(x)/ΨSqₙ(x), ωₙ(x,y)/ψₙ(x,y)³)` satisfies `W.Equation`; equivalently that
  `W.polynomial.eval₂ _ _ = 0`, which is the `AdjoinRoot.lift` obligation `#403`/`#405` need.
* ❌ **The `ωₙ` duplication formula** — `n • (x, y) = (Φₙ(x)/ΨSqₙ(x), ωₙ(x,y)/(2 ψₙ(x,y)³))`, the
  **group-law** multiple and not merely *some* point of the curve.  This is **`#251`**, it is
  **open**, and `#404` never claimed it.

The closed half is `WeierstrassCurve.hasPreΩSq` (every index, every `CommRing`) and
`WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero` (the identity itself, over a field of
characteristic `≠ 2`, with `ψₙ(x, y) ≠ 0`), both in `EllipticCurves.Torsion.OmegaCrux`; the
`Φ`/`ΨSq` phrasing is `WeierstrassCurve.hasΨSqDoubling`.  ⚠️ `OmegaCrux` is **not** in this file's
import closure, so those three names are not resolvable here and nothing below uses them; they are
cited, not consumed.

⚠️ **The open half was never `#404`'s.**  `equation_div_of_ψ_ne_zero` says the coordinates lie on
the curve; it says nothing about `n • P`, and its own docstring records that.  Identifying the two
is `WeierstrassCurve.Affine.HasXCoordFormula` (`EllipticCurves.Torsion.NsmulSurjective`), issue
`#251`, available at `n = 2` and `n = 3` only (`hasXCoordFormula_two`, `hasXCoordFormula_three`),
with the `y`-half `addY_self_eq_div` / `addY_add_self_eq_div`
(`EllipticCurves.Torsion.DoublingCoords`, `EllipticCurves.Torsion.TriplingCoords`) likewise.

⚠️ **So a bullet that needs the group-law multiple in division-polynomial form is still gated — on
`#251`, and the gate must be relettered rather than removed.**  A bullet that needs only the
on-curve identity is discharged.  ⚠️ `#1184` (`IsCoprime (Φₙ) (ΨSqₙ)` at general `n`) and `#962`
(`hprin` over a general field) are untouched by PR #557 and stay open; where they are listed
alongside `#404`, only `#404`'s name comes off.

## Main definitions

* `WeierstrassCurve.Affine.Point.xCoord`, `Point.yCoord` — the coordinates of a point, with the
  junk value `0` at the point at infinity.
* `WeierstrassCurve.Affine.CoordinateRing.pointCoordHom` — for an affine point `(x, y)` of
  `W ⁄ F(W)`, the ring homomorphism `F[W] →+* F(W)` sending the generic point to `(x, y)`.
* `…pointAlgHom` — the same as an `F`-algebra homomorphism.
* `…pointEndo` — the induced endomorphism `F(W) →+* F(W)`, for `x` transcendental over `F`.
* `…mulByNCoordHom`, `…mulByNEndo` — the specialisation at the point `n • 𝒫`.
* `…mulByNEndoAlgHom` — `[n]∗` as an `F`-algebra endomorphism of `F(W)`, which is the form
  `genPointHom` consumes.  It lives here, beside its own `commutes'` field
  `mulByNEndo_algebraMap_base`, exactly as `#699` placed `mulByTwoEndoAlgHom` in `MulByTwoFinite`
  and `TranslationTriplingCommGeneral` placed `mulByThreeEndoAlgHom` in `MulByThreeFinite`.

## Main statements

* `…pointCoordHom_injective` — `pointCoordHom` is injective as soon as `x` is transcendental over
  `F`.  ⚠️ This is the *only* place a hypothesis beyond the group law is used, and it is exactly the
  dominance step `mulByTwoCoordHom_injective` / `mulByThreeCoordHom_injective` perform by an
  explicit degree count on `Φₙ`/`ΨSqₙ`.
* `…functionField_ringHom_ext` — two ring homomorphisms out of `F(W)` into an arbitrary field,
  fixing `F` and agreeing on `genX` and `genY`, are equal.
* `…nsmul_genericPoint_eq` — the bridge `[n]∗` *realises* `𝒫 ↦ n • 𝒫`.
* `…mulByNEndo_injective` — `[n]∗` is injective.
* `…mulByNEndo_one`, `…mulByNEndo_two`, `…mulByNEndo_three` — the identity, `mulByTwoEndo` and
  `mulByThreeEndo`.

## ⚠️ One `@[simp]` attribute was removed here, and the lemma kept (`#1278`)

`pointCoordHom_X` carried `@[simp]` and **could never fire**: its LHS is `mk W (C X)`, and
`AdjoinRoot.mk_C` — itself `@[simp]` — rewrites that to `AdjoinRoot.of W.polynomial X` before the
pattern is tried. Measured with Mathlib's `simpNF` environment linter, which had never been run on
this tree. The lemma is unchanged and still used by name below.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.4, III.6, III.8.
-/

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

namespace Point

variable {R : Type*} [CommRing R] {W' : Affine R}

/-- The `x`-coordinate of a point of `W'`, with the junk value `0` at the point at infinity. -/
def xCoord : W'.Point → R
  | .zero => 0
  | .some x _ _ => x

/-- The `y`-coordinate of a point of `W'`, with the junk value `0` at the point at infinity. -/
def yCoord : W'.Point → R
  | .zero => 0
  | .some _ y _ => y

@[simp] lemma xCoord_some {x y : R} (h : W'.Nonsingular x y) :
    (Point.some x y h).xCoord = x := rfl

@[simp] lemma yCoord_some {x y : R} (h : W'.Nonsingular x y) :
    (Point.some x y h).yCoord = y := rfl

@[simp] lemma xCoord_zero : (0 : W'.Point).xCoord = 0 := rfl

@[simp] lemma yCoord_zero : (0 : W'.Point).yCoord = 0 := rfl

/-- A point other than the point at infinity is nonsingular at its own coordinates. -/
lemma nonsingular_of_ne_zero {P : W'.Point} (hP : P ≠ 0) :
    W'.Nonsingular P.xCoord P.yCoord := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => exact h

/-- A point other than the point at infinity is `Point.some` at its own coordinates. -/
lemma eq_some_of_ne_zero {P : W'.Point} (hP : P ≠ 0) :
    P = .some P.xCoord P.yCoord (nonsingular_of_ne_zero hP) := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => rfl

/-- A point other than the point at infinity lies on the curve at its own coordinates. -/
lemma equation_of_ne_zero {P : W'.Point} (hP : P ≠ 0) : W'.Equation P.xCoord P.yCoord :=
  (nonsingular_of_ne_zero hP).left

end Point

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

/-! ### The coordinate-ring homomorphism attached to a point of `W ⁄ F(W)` -/

/-- **The pullback along a point of `W ⁄ F(W)`, coordinate-ring half.**  An affine point `(x, y)` of
the base-changed curve determines the ring homomorphism `F[W] →+* F(W)` sending the generic point
`𝒫 = (genX W, genY W)` to `(x, y)`.

It is `AdjoinRoot.lift` of `x` and `y`, whose single well-definedness obligation
`W.polynomial.eval₂ _ _ = 0` is *exactly* the hypothesis `h`: that `(x, y)` lies on the curve.  ⚠️
When `(x, y)` comes from a `Point`, `h` is a projection of the point's own `Nonsingular` field, so
no equation has to be proved — this is what makes the general `n` construction below independent of
the `ωₙ` crux (`#404`, since closed by PR #557 and now
`WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero`; independence, not a gate). -/
noncomputable def pointCoordHom {x y : W.FunctionField}
    (h : (W.map (algebraMap F W.FunctionField)).Equation x y) :
    W.CoordinateRing →+* W.FunctionField :=
  AdjoinRoot.lift (eval₂RingHom (algebraMap F W.FunctionField) x) y
    (by rw [eval₂_eval₂RingHom_apply, ← map_polynomial]; exact h)

lemma pointCoordHom_X {x y : W.FunctionField}
    (h : (W.map (algebraMap F W.FunctionField)).Equation x y) :
    pointCoordHom h (mk W (C Polynomial.X)) = x := by
  rw [pointCoordHom, show mk W (C Polynomial.X) = AdjoinRoot.of W.polynomial Polynomial.X from rfl,
    AdjoinRoot.lift_of, coe_eval₂RingHom, eval₂_X]

@[simp] lemma pointCoordHom_root {x y : W.FunctionField}
    (h : (W.map (algebraMap F W.FunctionField)).Equation x y) :
    pointCoordHom h (AdjoinRoot.root W.polynomial) = y := by
  rw [pointCoordHom, AdjoinRoot.lift_root]

/-- `pointCoordHom` fixes the image of `F`. -/
lemma pointCoordHom_algebraMap {x y : W.FunctionField}
    (h : (W.map (algebraMap F W.FunctionField)).Equation x y) (c : F) :
    pointCoordHom h (algebraMap F W.CoordinateRing c) = algebraMap F W.FunctionField c := by
  have h1 : (algebraMap F W.CoordinateRing c) = mk W (C (C c)) := by
    rw [IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing, AdjoinRoot.algebraMap_eq,
      ← Polynomial.C_eq_algebraMap]; rfl
  rw [h1, show mk W (C (C c)) = AdjoinRoot.of W.polynomial (C c) from rfl, pointCoordHom,
    AdjoinRoot.lift_of, coe_eval₂RingHom, eval₂_C]

/-- `pointCoordHom` packaged as an `F`-algebra homomorphism. -/
noncomputable def pointAlgHom {x y : W.FunctionField}
    (h : (W.map (algebraMap F W.FunctionField)).Equation x y) :
    W.CoordinateRing →ₐ[F] W.FunctionField where
  toRingHom := pointCoordHom h
  commutes' := pointCoordHom_algebraMap h

@[simp] lemma pointAlgHom_apply {x y : W.FunctionField}
    (h : (W.map (algebraMap F W.FunctionField)).Equation x y) (a : W.CoordinateRing) :
    pointAlgHom h a = pointCoordHom h a := rfl

/-- **Dominance.**  `pointCoordHom h` is injective as soon as its `x`-image is transcendental over
`F`.  A non-injective `F`-algebra map out of `F[W]` has a nonzero prime — hence maximal, as `F[W]`
has Krull dimension `≤ 1` — kernel, so by Zariski's lemma (`isAlgebraic_of_ker_maximal`) its whole
image is algebraic over `F`; in particular `x` would be.

⚠️ This is the same step `mulByTwoCoordHom_injective` and `mulByThreeCoordHom_injective` take, with
the concrete degree count on `Φₙ`/`ΨSqₙ` that establishes transcendence at `n = 2, 3` replaced by a
hypothesis. -/
lemma pointCoordHom_injective {x y : W.FunctionField}
    (h : (W.map (algebraMap F W.FunctionField)).Equation x y) (hx : Transcendental F x) :
    Function.Injective (pointCoordHom h) := by
  have key : Function.Injective (pointAlgHom h) := by
    by_contra hni
    have hne : RingHom.ker (pointAlgHom h) ≠ ⊥ := fun hk =>
      hni ((RingHom.injective_iff_ker_eq_bot _).mpr hk)
    haveI hprime : (RingHom.ker (pointAlgHom h)).IsPrime := RingHom.ker_isPrime _
    have hmax : (RingHom.ker (pointAlgHom h)).IsMaximal := hprime.isMaximal hne
    have hu : IsAlgebraic F (pointAlgHom h (mk W (C Polynomial.X))) :=
      isAlgebraic_of_ker_maximal (pointAlgHom h) hmax (mk W (C Polynomial.X))
    rw [pointAlgHom_apply, pointCoordHom_X] at hu
    exact hx hu
  exact key

/-- **The pullback along a point of `W ⁄ F(W)`.**  The ring endomorphism `F(W) →+* F(W)` sending
the generic point to `(x, y)`, obtained from the injective coordinate-ring pullback by the universal
property of the fraction field. -/
noncomputable def pointEndo {x y : W.FunctionField}
    (h : (W.map (algebraMap F W.FunctionField)).Equation x y) (hx : Transcendental F x) :
    W.FunctionField →+* W.FunctionField :=
  IsFractionRing.lift (pointCoordHom_injective h hx)

@[simp] lemma pointEndo_algebraMap {x y : W.FunctionField}
    (h : (W.map (algebraMap F W.FunctionField)).Equation x y) (hx : Transcendental F x)
    (a : W.CoordinateRing) :
    pointEndo h hx (algebraMap W.CoordinateRing W.FunctionField a) = pointCoordHom h a :=
  IsFractionRing.lift_algebraMap (pointCoordHom_injective h hx) a

@[simp] lemma pointEndo_genX {x y : W.FunctionField}
    (h : (W.map (algebraMap F W.FunctionField)).Equation x y) (hx : Transcendental F x) :
    pointEndo h hx (genX W) = x := by
  conv_lhs => rw [genX, genPsi]
  rw [pointEndo_algebraMap, pointCoordHom_X]

@[simp] lemma pointEndo_genY {x y : W.FunctionField}
    (h : (W.map (algebraMap F W.FunctionField)).Equation x y) (hx : Transcendental F x) :
    pointEndo h hx (genY W) = y := by
  conv_lhs => rw [genY, genPsi]
  rw [pointEndo_algebraMap, pointCoordHom_root]

/-- `pointEndo` fixes the constants. -/
lemma pointEndo_algebraMap_base {x y : W.FunctionField}
    (h : (W.map (algebraMap F W.FunctionField)).Equation x y) (hx : Transcendental F x) (c : F) :
    pointEndo h hx (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c := by
  rw [IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField, pointEndo_algebraMap,
    pointCoordHom_algebraMap]
  exact IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField c

/-! ### Extensionality through the two coordinate generators -/

lemma genX_def : genX W = genPsi W (mk W (C Polynomial.X)) := rfl

lemma genY_def : genY W = genPsi W (AdjoinRoot.root W.polynomial) := rfl

/-- **Two ring homomorphisms out of `F(W)` fixing `F` and agreeing on `genX` and `genY` are
equal.**  The two-step transfer `AdjoinRoot.ringHom_ext` then `IsFractionRing.ringHom_ext` that
several files in this directory perform inline; `genX` and `genY` generate `F[W]` over `F` and
`F(W)` is its fraction field.

⚠️ The target `L` is an arbitrary field and need **not** be `F(W)`: the proof never composes `f`
with itself, and `IsFractionRing.ringHom_ext` is already stated at an arbitrary target field.  The
endomorphism case `L = F(W)` is what `TranslationDoublingCommGeneral` and `MulByNPullback` use;
`EllipticCurves.FunctionField.FunctionFieldBaseChangeN` needs the case `L = K(W⁄K)`, which is why
the statement is at this generality rather than the one the first consumer asked for. -/
lemma functionField_ringHom_ext {L : Type*} [Field L] {f g : W.FunctionField →+* L}
    (hc : ∀ c : F, f (algebraMap F W.FunctionField c) = g (algebraMap F W.FunctionField c))
    (hX : f (genX W) = g (genX W)) (hY : f (genY W) = g (genY W)) : f = g := by
  have key : f.comp (genPsi W) = g.comp (genPsi W) := by
    refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun c => ?_) ?_) ?_
    · simpa only [RingHom.comp_apply, show (AdjoinRoot.of W.polynomial (C c)) = mk W (C (C c)) from
        rfl, genPsi_mk_CC] using hc c
    · simpa only [RingHom.comp_apply, show (AdjoinRoot.of W.polynomial Polynomial.X)
        = mk W (C Polynomial.X) from rfl, ← genX_def] using hX
    · simpa only [RingHom.comp_apply, ← genY_def] using hY
  exact IsFractionRing.ringHom_ext (A := W.CoordinateRing) fun a => RingHom.congr_fun key a

/-! ### The multiplication-by-`n` pullback -/

variable [W.IsElliptic]

omit [W.IsElliptic] in
/-- A point whose `x`-coordinate is transcendental over `F` is not the point at infinity, whose
`x`-coordinate is the constant `0`. -/
lemma ne_zero_of_transcendental_xCoord
    {P : (W.map (algebraMap F W.FunctionField)).Point} (h : Transcendental F P.xCoord) :
    P ≠ 0 := by
  rintro rfl
  exact h isAlgebraic_zero

/-- **The multiplication-by-`n` pullback, coordinate-ring half**, for `n : ℕ`.  It sends the generic
point `𝒫` to `n • 𝒫`, the multiple being taken in the Mathlib group `(W ⁄ F(W)).Point`.  ⚠️ The
hypothesis is on the `x`-coordinate of `n • 𝒫` only, and it is what says `[n]` is non-constant; the
fact that `n • 𝒫` lies on the curve is carried by the point itself. -/
noncomputable def mulByNCoordHom (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) :
    W.CoordinateRing →+* W.FunctionField :=
  pointCoordHom (Point.equation_of_ne_zero (ne_zero_of_transcendental_xCoord hn))

/-- **The multiplication-by-`n` endomorphism `[n]∗ : F(W) →+* F(W)`**, for `n : ℕ` such that the
`x`-coordinate of `n • 𝒫` is transcendental over `F`. -/
noncomputable def mulByNEndo (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) :
    W.FunctionField →+* W.FunctionField :=
  pointEndo (Point.equation_of_ne_zero (ne_zero_of_transcendental_xCoord hn)) hn

@[simp] lemma mulByNEndo_genX (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) :
    mulByNEndo n hn (genX W) = (n • genericPoint (W := W)).xCoord :=
  pointEndo_genX _ hn

@[simp] lemma mulByNEndo_genY (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) :
    mulByNEndo n hn (genY W) = (n • genericPoint (W := W)).yCoord :=
  pointEndo_genY _ hn

lemma mulByNEndo_algebraMap_base (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) (c : F) :
    mulByNEndo n hn (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c :=
  pointEndo_algebraMap_base _ _ c

/-- **`[n]∗` as an `F`-algebra endomorphism of `F(W)`.**  `mulByNEndo` is a bare `RingHom`; the
generic-point transport of `TranslationMulByNCommGeneral` (`Point.map`, through `genPointHom`)
needs an `F`-algebra endomorphism.  It is `mulByNEndo` together with `mulByNEndo_algebraMap_base`,
and it lives here — beside its own `commutes'` field — following the placement `#699` chose for
`mulByTwoEndoAlgHom` and `TranslationTriplingCommGeneral` chose for `mulByThreeEndoAlgHom`. -/
noncomputable def mulByNEndoAlgHom (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) :
    W.FunctionField →ₐ[F] W.FunctionField where
  toRingHom := mulByNEndo n hn
  commutes' := mulByNEndo_algebraMap_base n hn

@[simp] lemma mulByNEndoAlgHom_apply (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) (f : W.FunctionField) :
    mulByNEndoAlgHom n hn f = mulByNEndo n hn f := rfl

/-- `[n]∗` is injective: it is a ring homomorphism out of a field. -/
lemma mulByNEndo_injective (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) :
    Function.Injective (mulByNEndo n hn) :=
  (mulByNEndo n hn).injective

lemma nonsingular_mulByNEndo_gen (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) :
    (W.map (algebraMap F W.FunctionField)).Nonsingular
      (mulByNEndo n hn (genX W)) (mulByNEndo n hn (genY W)) := by
  rw [mulByNEndo_genX, mulByNEndo_genY]
  exact Point.nonsingular_of_ne_zero (ne_zero_of_transcendental_xCoord hn)

/-- **The bridge `[n]∗ = [n]•`.**  The multiplication-by-`n` endomorphism acts on the coordinate
generators of `F(W)` exactly as `n •` in the group `(W ⁄ F(W)).Point`:

```
n • 𝒫 = (mulByNEndo n hn (genX W), mulByNEndo n hn (genY W)).
```

This is the general `n` form of the merged `genericPoint_add_self` (`n = 2`) and
`genericPoint_add_add_self` (`n = 3`), and here it holds **by construction** rather than by a
division-polynomial computation. -/
theorem nsmul_genericPoint_eq (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) :
    n • genericPoint (W := W)
      = Point.some (mulByNEndo n hn (genX W)) (mulByNEndo n hn (genY W))
          (nonsingular_mulByNEndo_gen n hn) := by
  conv_lhs => rw [Point.eq_some_of_ne_zero (ne_zero_of_transcendental_xCoord hn)]
  rw [Point.some.injEq]
  exact ⟨(mulByNEndo_genX n hn).symm, (mulByNEndo_genY n hn).symm⟩

/-! ### The low-index cases, against the merged division-polynomial endomorphisms -/

lemma xCoord_one_nsmul_genericPoint : (1 • genericPoint (W := W)).xCoord = genX W := by
  rw [one_nsmul]; rfl

lemma yCoord_one_nsmul_genericPoint : (1 • genericPoint (W := W)).yCoord = genY W := by
  rw [one_nsmul]; rfl

/-- At `n = 1` the hypothesis is the merged `transcendental_genX`. -/
lemma transcendental_xCoord_one_nsmul :
    Transcendental F (1 • genericPoint (W := W)).xCoord := by
  rw [xCoord_one_nsmul_genericPoint]; exact transcendental_genX

/-- `[1]∗` is the identity. -/
theorem mulByNEndo_one :
    mulByNEndo 1 (transcendental_xCoord_one_nsmul (W := W)) = RingHom.id W.FunctionField := by
  refine functionField_ringHom_ext (fun c => ?_) ?_ ?_
  · rw [RingHom.id_apply]; exact mulByNEndo_algebraMap_base _ _ c
  · rw [RingHom.id_apply, mulByNEndo_genX, xCoord_one_nsmul_genericPoint]
  · rw [RingHom.id_apply, mulByNEndo_genY, yCoord_one_nsmul_genericPoint]

lemma xCoord_two_nsmul_genericPoint (h2 : (2 : F) ≠ 0) :
    (2 • genericPoint (W := W)).xCoord = mulByTwoEndo h2 (genX W) := by
  rw [two_nsmul, genericPoint_add_self h2]; rfl

lemma yCoord_two_nsmul_genericPoint (h2 : (2 : F) ≠ 0) :
    (2 • genericPoint (W := W)).yCoord = mulByTwoEndo h2 (genY W) := by
  rw [two_nsmul, genericPoint_add_self h2]; rfl

/-- At `n = 2` the hypothesis is the dominance step of `MulByTwoEndomorphism.lean`. -/
lemma transcendental_xCoord_two_nsmul (h2 : (2 : F) ≠ 0) :
    Transcendental F (2 • genericPoint (W := W)).xCoord := by
  rw [xCoord_two_nsmul_genericPoint h2]
  intro hu
  exact transcendental_genX (isAlgebraic_genX_of_two h2
    (by rwa [mulByTwoCoordHom_X, ← mulByTwoEndo_genX h2]))

/-- **`[2]∗` built from the group law is the merged `mulByTwoEndo`.** -/
theorem mulByNEndo_two (h2 : (2 : F) ≠ 0) :
    mulByNEndo 2 (transcendental_xCoord_two_nsmul (W := W) h2) = mulByTwoEndo h2 := by
  refine functionField_ringHom_ext (fun c => ?_) ?_ ?_
  · rw [mulByNEndo_algebraMap_base, IsScalarTower.algebraMap_apply F W.CoordinateRing
      W.FunctionField, mulByTwoEndo_algebraMap, mulByTwoCoordHom_algebraMap,
      ← IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField]
  · rw [mulByNEndo_genX, xCoord_two_nsmul_genericPoint h2]
  · rw [mulByNEndo_genY, yCoord_two_nsmul_genericPoint h2]

lemma xCoord_three_nsmul_genericPoint (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    (3 • genericPoint (W := W)).xCoord = mulByThreeEndo h2 h3 (genX W) := by
  rw [three_nsmul, add_comm, genericPoint_add_add_self h2 h3]; rfl

lemma yCoord_three_nsmul_genericPoint (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    (3 • genericPoint (W := W)).yCoord = mulByThreeEndo h2 h3 (genY W) := by
  rw [three_nsmul, add_comm, genericPoint_add_add_self h2 h3]; rfl

/-- At `n = 3` the hypothesis is the dominance step of `MulByThreeEndomorphism.lean`. -/
lemma transcendental_xCoord_three_nsmul (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Transcendental F (3 • genericPoint (W := W)).xCoord := by
  rw [xCoord_three_nsmul_genericPoint h2 h3]
  intro hu
  exact transcendental_genX (isAlgebraic_genX_of_three h2 h3
    (by rwa [mulByThreeCoordHom_X, ← mulByThreeEndo_genX h2 h3]))

/-- **`[3]∗` built from the group law is the merged `mulByThreeEndo`.** -/
theorem mulByNEndo_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    mulByNEndo 3 (transcendental_xCoord_three_nsmul (W := W) h2 h3) = mulByThreeEndo h2 h3 := by
  refine functionField_ringHom_ext (fun c => ?_) ?_ ?_
  · rw [mulByNEndo_algebraMap_base, IsScalarTower.algebraMap_apply F W.CoordinateRing
      W.FunctionField, mulByThreeEndo_algebraMap, mulByThreeCoordHom_algebraMap,
      ← IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField]
  · rw [mulByNEndo_genX, xCoord_three_nsmul_genericPoint h2 h3]
  · rw [mulByNEndo_genY, yCoord_three_nsmul_genericPoint h2 h3]

end CoordinateRing

end WeierstrassCurve.Affine
