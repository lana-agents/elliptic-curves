/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.FunctionFieldBaseChange
import EllipticCurves.FunctionField.MulByNPullback
import EllipticCurves.FunctionField.TranslationPointEndomorphism

/-!
# Base change of `[n]∗` and `τ_P∗` at general `n`

`EllipticCurves.FunctionField.FunctionFieldBaseChange` transports the endomorphisms of `F(W)`
along the base-change map `functionFieldMap W K : F(W) →+* K(W⁄K)` — but only at the two numerals
it had available, `functionFieldMap_mulByTwoEndo` and `functionFieldMap_mulByThreeEndo`.  There was
no general-`n` form, and that single gap is what stood between the merged general-`n` alternating
assembly (`EllipticCurves.FunctionField.WeilPairingAlternatingAssemblyN`) and the alternating
property over an **arbitrary** field.  This file closes it.

## The idea, which is not the numeral proof

The merged numeral intertwiners are coordinate computations: `mulByTwoEndo` sends `genX` to
`Φ₂/Ψ₂²` and `genY` to an explicit rational expression, and the proofs push `functionFieldMap`
through those formulas term by term (`functionFieldMap_Φ_eval`, `functionFieldMap_ΨSq_eval`, …).
At general `n` no such formula is available *here*.  ⚠️ This sentence used to blame `#251`, which
is **closed** — `hasXCoordFormula_of_two_ne_zero` (`EllipticCurves.Torsion.NsmulOrder`) and its
`y`-half `nsmul_eq_some_omegaY_of_ΨSq_ne_zero` (`EllipticCurves.Torsion.NsmulYPeriodic`, `#1500`)
give both coordinates of `n • P` at every index with `(2 : F) ≠ 0`, on the **curve**.  ⚠️ What is
missing is the *function-field* intertwiner `functionFieldMap_mulByNEndo`, and whether the affine
formula supplies it is **not measured**: `mulByNEndo` is not defined by a formula (see below).

`mulByNEndo n hn` is not defined by a formula.  It is `pointEndo` at the point `n • 𝒫`, so it is
pinned by
```
[n]∗ genX = (n • 𝒫).xCoord      and      [n]∗ genY = (n • 𝒫).yCoord ,
```
and the intertwining is therefore not a coordinate identity at all but a **group** one:
base change acts on `(W ⁄ F(W)).Point` as an additive map (`functionFieldPointMap`), it sends `𝒫`
to `𝒫` because it fixes both generators (`functionFieldMap_genX`, `functionFieldMap_genY`), and an
additive map sending `𝒫` to `𝒫` sends `n • 𝒫` to `n • 𝒫`.  Reading off coordinates gives
`functionFieldMap_xCoord_nsmul` and its `yCoord` twin, and `functionField_ringHom_ext` turns those
two equations into the intertwiner.

This is `EllipticCurves.FunctionField.WeilPairingGaloisRootN`'s argument for `σ⋆`, transplanted:
there the additive map is a Galois action of `F(W)` on itself, here it is base change between two
*different* function fields.  ⚠️ The transport hazard that costs elsewhere does not arise:
`W.map (algebraMap F K(W⁄K))` and `(W⁄K).map (algebraMap K K(W⁄K))` are **`rfl`-equal**, so
Mathlib's `WeierstrassCurve.Affine.Point.map` lands literally on the type where `𝒫` over `K` lives,
with no `▸` and no `Eq.mpr`.

## ⚠️ Two transcendence hypotheses, over two different fields, and neither implies the other

`mulByNEndo` is indexed by its own non-constancy datum, so `functionFieldMap_mulByNEndo` takes
`hn` over `F` **and** `hn'` over `K`.  This is the exact shape of the merged numeral forms, which
take `h2` and `h2'` for the same reason; `algebraMap_ofNat_ne_zero` produces the second there, and
here the second is produced by whichever of `transcendental_xCoord_nsmul_of_smooth` (any field) or
`transcendental_xCoord_nsmul_of_isAlgClosed` (over `F̄`) the caller can afford.  Do not try to
transport one into the other: `Transcendental F x` and `Transcendental K (functionFieldMap x)` are
statements about different fields and the first does not imply the second in this generality.

## ⚠️ The recovery is *not* verbatim, and the missing binder is a real finding

`#907` asks that the merged statements come back out of the general one.  Both do — **but with
`[W.IsElliptic]` added**, and that binder cannot be removed:

* `functionFieldMap_mulByTwoEndo` and `_mulByThreeEndo` carry **no** ellipticity hypothesis, because
  `mulByTwoEndo` is built from division polynomials, which exist for any Weierstrass curve;
* `mulByNEndo n hn` cannot even be *stated* without it, since its index `hn` mentions
  `genericPoint`, and `genericPoint` is defined only for `[W.IsElliptic]`.

So the general form is strictly weaker than the merged numerals at `n = 2, 3` in exactly one binder,
and the `Recovery` block below says so rather than hiding it behind an added hypothesis.  This is a
limitation of how `mulByNEndo` is indexed, not of the argument here, and it is invisible to every
consumer on the Weil-pairing front — all of them are already over an elliptic curve.

## Main statements

* `WeierstrassCurve.Affine.CoordinateRing.functionFieldMapAlgHom` — `functionFieldMap` as an
  `F`-algebra homomorphism, which is what `Point.map` asks for.
* `…functionFieldPointMap`, `…functionFieldPointMap_genericPoint` — base change on points of
  `W ⁄ F(W)`, and that it fixes the generic point.
* `…functionFieldMap_xCoord_nsmul`, `…functionFieldMap_yCoord_nsmul` — the coordinates of `n • 𝒫`
  transport, at every `n`.
* **`…functionFieldMap_mulByNEndo`** — the new brick: base change intertwines `[n]∗`, at every
  `n` at which `[n]` is non-constant **over `F` and over `K`**.
* `…basePointMap`, `…functionFieldMap_translatePointEndo` — the `W.Point`-indexed translation
  intertwiner, which is `functionFieldMap_translateEndo` extended over the point at infinity.  It is
  what a general-`n` descent needs, because the general-`n` telescope is indexed by `i • T` rather
  than by an affine pair.

⚠️ **The non-constancy is named in that one row and in no other, because no other row binds it.**
`functionFieldMap_mulByNEndo` is the only declaration listed above with a propositional hypothesis
at all, and it takes **two** — `hn` over `F` and `hn'` over `K` — which is exactly what the section
above says cannot be reduced to one.  `xCoord_zero` makes each of them false at `n = 0`, so a
clause reading *"at every `n`"* over that pair is short on the index axis, which is the omission
`README.md` `### Reach clauses` convicts by name in `ramificationIdxN_pos`, over the same binder in
the same argument position.  ⚠️ Until `#1658` this row's clause stopped at *"base change
intertwines `[n]∗` at every `n`"* (`b821a45`, `#1333`), naming neither.

⚠️ **No head-of-list register is written**, and the `DeterminantModGeneral` form (`README.md`
`### Module-block bullets`) is not the repair here: every other declaration listed above binds no
propositional hypothesis whatever, so a register saying every statement below takes the
non-constancy would be false of all of them — `#1636`'s finding, in its strongest form.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.4, III.8.
-/

open Polynomial

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} {K : Type*} [Field K] [Algebra F K]

/-! ### Base change as a map of points -/

variable (W K) in
/-- **`functionFieldMap` as an `F`-algebra homomorphism.**  It is a bare `→+*` by design (this
file's predecessor registers no `Algebra F(W) K(W⁄K)` instance), but it does fix `F`, and
`Point.map` asks for an `S`-algebra map. -/
noncomputable def functionFieldMapAlgHom :
    W.FunctionField →ₐ[F] (W.map (algebraMap F K)).FunctionField where
  toRingHom := functionFieldMap W K
  commutes' c := by
    rw [IsScalarTower.algebraMap_apply F K (W.map (algebraMap F K)).FunctionField]
    exact functionFieldMap_algebraMap_base W K c

@[simp] lemma functionFieldMapAlgHom_apply (z : W.FunctionField) :
    functionFieldMapAlgHom W K z = functionFieldMap W K z :=
  rfl

/-- Base change carries points of `W ⁄ F(W)` to points of `W⁄K ⁄ K(W⁄K)`: the curve transports
(`map_map_functionFieldMap`) and `functionFieldMap` is injective. -/
lemma nonsingular_functionFieldMap {x y : W.FunctionField}
    (h : (W.map (algebraMap F W.FunctionField)).Nonsingular x y) :
    ((W.map (algebraMap F K)).map
        (algebraMap K (W.map (algebraMap F K)).FunctionField)).Nonsingular
      (functionFieldMap W K x) (functionFieldMap W K y) := by
  have key := ((W.map (algebraMap F W.FunctionField)).map_nonsingular
    (f := (functionFieldMap W K : W.FunctionField →+*
      (W.map (algebraMap F K)).FunctionField)) (functionFieldMap W K).injective x y).mpr h
  rwa [map_map_functionFieldMap] at key

variable (W K) in
/-- **The action of base change on `(W ⁄ F(W)).Point`, as an `AddMonoidHom`.**  Mathlib's
`WeierstrassCurve.Affine.Point.map` at `functionFieldMapAlgHom`.  Being additive is the whole
content: it is what lets base change be pushed through `n • 𝒫`.

⚠️ No transport is needed, because `W.map (algebraMap F K(W⁄K))` and
`(W⁄K).map (algebraMap K K(W⁄K))` are `rfl`-equal. -/
noncomputable def functionFieldPointMap :
    (W.map (algebraMap F W.FunctionField)).Point →+
      ((W.map (algebraMap F K)).map
        (algebraMap K (W.map (algebraMap F K)).FunctionField)).Point :=
  Point.map (W' := W) (functionFieldMapAlgHom W K)

/-- `functionFieldPointMap` acts on an affine point by base-changing both coordinates. -/
lemma functionFieldPointMap_some {x y : W.FunctionField}
    (h : (W.map (algebraMap F W.FunctionField)).Nonsingular x y) :
    functionFieldPointMap W K (Point.some x y h)
      = Point.some (functionFieldMap W K x) (functionFieldMap W K y)
        (nonsingular_functionFieldMap h) :=
  rfl

open Classical in
variable (W K) in
/-- **Base change on `W.Point`.**  Mathlib's `Point.map` at `Algebra.ofId F K`; the `F → K`
analogue of `torsionPointMap`, which is the same gadget for `F → F(W)`. -/
noncomputable def basePointMap : W.Point →+ (W.map (algebraMap F K)).Point :=
  Point.map (W' := W) (Algebra.ofId F K)

open Classical in
@[simp] lemma basePointMap_some {x y : F} (h : W.Nonsingular x y) :
    basePointMap W K (Point.some x y h)
      = Point.some (algebraMap F K x) (algebraMap F K y)
        ((map_nonsingular W (f := algebraMap F K) (algebraMap F K).injective x y).mpr h) :=
  rfl

variable [W.IsElliptic]

variable (W K) in
/-- **Base change fixes the generic point**, because it fixes both of its coordinates
(`functionFieldMap_genX`, `functionFieldMap_genY`).

⚠️ `rw [Point.some.injEq]` is the wrong tool here — the two curve expressions are definitionally
equal only at `default` transparency and `rw` elaborates at `instances`.  `congr 1` does the job,
proof irrelevance closing the `Nonsingular` component. -/
lemma functionFieldPointMap_genericPoint :
    functionFieldPointMap W K (genericPoint (W := W))
      = genericPoint (W := W.map (algebraMap F K)) := by
  rw [genericPoint, functionFieldPointMap_some]
  congr 1
  · exact functionFieldMap_genX W K
  · exact functionFieldMap_genY W K

variable (W K) in
/-- Base change sends `n • 𝒫` to `n • 𝒫`, at every `n`: `functionFieldPointMap` is additive and
fixes `𝒫`. -/
lemma functionFieldPointMap_nsmul_genericPoint (n : ℕ) :
    functionFieldPointMap W K (n • genericPoint (W := W))
      = n • genericPoint (W := W.map (algebraMap F K)) := by
  rw [map_nsmul, functionFieldPointMap_genericPoint]

variable (W K) in
/-- **The `x`-coordinate of `n • 𝒫` transports, at every `n`.**  At the point at infinity both
sides are the junk value `0`. -/
lemma functionFieldMap_xCoord_nsmul (n : ℕ) :
    functionFieldMap W K ((n • genericPoint (W := W)).xCoord)
      = (n • genericPoint (W := W.map (algebraMap F K))).xCoord := by
  have h := functionFieldPointMap_nsmul_genericPoint W K n
  cases hc : (n • genericPoint (W := W)) with
  | zero =>
      have h0 : (n • genericPoint (W := W.map (algebraMap F K))) = 0 := by
        rw [← h, hc]; exact map_zero _
      rw [h0]; exact map_zero _
  | some x y hns =>
      rw [hc, functionFieldPointMap_some] at h
      rw [← h, Point.xCoord_some, Point.xCoord_some]

variable (W K) in
/-- **The `y`-coordinate of `n • 𝒫` transports, at every `n`.**  The twin of
`functionFieldMap_xCoord_nsmul`. -/
lemma functionFieldMap_yCoord_nsmul (n : ℕ) :
    functionFieldMap W K ((n • genericPoint (W := W)).yCoord)
      = (n • genericPoint (W := W.map (algebraMap F K))).yCoord := by
  have h := functionFieldPointMap_nsmul_genericPoint W K n
  cases hc : (n • genericPoint (W := W)) with
  | zero =>
      have h0 : (n • genericPoint (W := W.map (algebraMap F K))) = 0 := by
        rw [← h, hc]; exact map_zero _
      rw [h0]; exact map_zero _
  | some x y hns =>
      rw [hc, functionFieldPointMap_some] at h
      rw [← h, Point.yCoord_some, Point.yCoord_some]

/-! ### The multiplication-by-`n` intertwiner -/

/-- **Base change intertwines the multiplication-by-`n` endomorphism, at every `n`.**

The general-`n` form of `functionFieldMap_mulByTwoEndo` and `functionFieldMap_mulByThreeEndo`.
`[n]∗` fixes the constants and sends the two coordinate generators to the coordinates of `n • 𝒫`,
so `functionField_ringHom_ext` reduces the statement to the two transports above.

⚠️ `hn` and `hn'` are hypotheses over **different** fields and neither implies the other; see the
module docstring. -/
theorem functionFieldMap_mulByNEndo {n : ℕ}
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hn' : Transcendental K (n • genericPoint (W := W.map (algebraMap F K))).xCoord)
    (z : W.FunctionField) :
    functionFieldMap W K (mulByNEndo n hn z)
      = mulByNEndo n hn' (functionFieldMap W K z) := by
  have key : (functionFieldMap W K).comp (mulByNEndo n hn)
      = (mulByNEndo n hn').comp (functionFieldMap W K) := by
    refine functionField_ringHom_ext (W := W) (fun c => ?_) ?_ ?_
    · simp only [RingHom.comp_apply, mulByNEndo_algebraMap_base, functionFieldMap_algebraMap_base]
    · simp only [RingHom.comp_apply, mulByNEndo_genX, functionFieldMap_genX,
        functionFieldMap_xCoord_nsmul]
    · simp only [RingHom.comp_apply, mulByNEndo_genY, functionFieldMap_genY,
        functionFieldMap_yCoord_nsmul]
  exact RingHom.congr_fun key z

/-! ### The translation intertwiner at a general point

`functionFieldMap_translateEndo` is indexed by an affine pair `(x₂, y₂)`.  The general-`n` divisor
telescope is indexed by `i • T` for `T : W.Point`, which is affine for no `i` in particular, so a
descent at general `n` needs the `W.Point`-indexed form below.
-/

open Classical in
/-- **Base change intertwines translation by an arbitrary point.**  Both branches of
`translatePointEndo` transport: at the point at infinity it is the identity on both sides, and at an
affine point it is `functionFieldMap_translateEndo`. -/
theorem functionFieldMap_translatePointEndo (P : W.Point) (z : W.FunctionField) :
    functionFieldMap W K (translatePointEndo P z)
      = translatePointEndo (basePointMap W K P) (functionFieldMap W K z) := by
  cases P with
  | zero =>
      rw [show (Point.zero : W.Point) = 0 from rfl, map_zero, translatePointEndo_zero,
        translatePointEndo_zero, RingHom.id_apply, RingHom.id_apply]
  | some x y h =>
      rw [basePointMap_some, translatePointEndo_some, translatePointEndo_some]
      exact functionFieldMap_translateEndo h.left z

/-! ### Recovery of the two merged numeral intertwiners

⚠️ **Not verbatim, and the difference is one instance binder.**  `functionFieldMap_mulByTwoEndo`
and `functionFieldMap_mulByThreeEndo` carry no `[W.IsElliptic]`; the statements below do, and it
cannot be dropped because `mulByNEndo`'s index mentions `genericPoint`.  See the module docstring.
Modulo that binder each is its merged twin character for character.
-/

section Recovery

/-- `functionFieldMap_mulByTwoEndo`, recovered — modulo `[W.IsElliptic]`. -/
private theorem functionFieldMap_mulByTwoEndo_of_general (h2 : (2 : F) ≠ 0) (h2' : (2 : K) ≠ 0)
    (z : W.FunctionField) :
    functionFieldMap W K (mulByTwoEndo h2 z)
      = mulByTwoEndo (W := W.map (algebraMap F K)) h2' (functionFieldMap W K z) := by
  have key := functionFieldMap_mulByNEndo (n := 2) (transcendental_xCoord_two_nsmul (W := W) h2)
    (transcendental_xCoord_two_nsmul (W := W.map (algebraMap F K)) h2') z
  rwa [mulByNEndo_two h2, mulByNEndo_two h2'] at key

/-- `functionFieldMap_mulByThreeEndo`, recovered — modulo `[W.IsElliptic]`. -/
private theorem functionFieldMap_mulByThreeEndo_of_general (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h2' : (2 : K) ≠ 0) (h3' : (3 : K) ≠ 0) (z : W.FunctionField) :
    functionFieldMap W K (mulByThreeEndo h2 h3 z)
      = mulByThreeEndo (W := W.map (algebraMap F K)) h2' h3' (functionFieldMap W K z) := by
  have key := functionFieldMap_mulByNEndo (n := 3)
    (transcendental_xCoord_three_nsmul (W := W) h2 h3)
    (transcendental_xCoord_three_nsmul (W := W.map (algebraMap F K)) h2' h3') z
  rwa [mulByNEndo_three h2 h3, mulByNEndo_three h2' h3'] at key

end Recovery

end CoordinateRing

end WeierstrassCurve.Affine
