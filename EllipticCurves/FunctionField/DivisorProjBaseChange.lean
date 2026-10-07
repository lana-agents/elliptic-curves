/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.DivisorBaseChange
import EllipticCurves.FunctionField.ProjectiveDivisor

/-!
# The projective divisor under base change of the function field

`EllipticCurves.FunctionField.DivisorBaseChange` transports `ord` and the affine `divisor` along
`functionFieldMap W K : F(W) → K(W⁄K)`, and says in its `## What is *not* here` that `divisorProj`
is not among them, because *"the point at infinity is not a height-one prime of `F[W]` and
`ordInfty` is a different object"*.  This file transports the remaining coordinate and assembles
the projective divisor.

## Why the point at infinity is a different argument, and a better one

At an affine closed point the transported order is multiplied by a ramification index, and
`DivisorBaseChange` proves only that the index is nonzero.  ⚠️ **At the point at infinity there is
no index at all: `ordInfty` is preserved on the nose.**  The reason is that `ordInfty` is not read
off a factorisation but computed from `deg`, and `deg` is the degree of an algebra norm over
`F[X]` — a determinant in the rank-two basis `{1, Y}`, which Mathlib computes as an explicit
polynomial in the two coordinates and the `aᵢ`.  Base change maps that polynomial to the same
polynomial over `K`, and `Polynomial.map` along an injective map preserves `natDegree`.  So the
whole argument is `norm_map` plus `natDegree_map`, and it needs neither a place nor a
`LiesOver`.

This is the statement that a constant field extension is **unramified at infinity**, in the form
this development can use it.  It is also the first coordinate of the base-change layer that
transports with no factor at all.

## Main definitions

* `WeierstrassCurve.Affine.CoordinateRing.projUnder` : the map `ProjPoint (W⁄K) → ProjPoint W`
  sending an affine closed point to the point of `W` it lies over and infinity to infinity.
* `WeierstrassCurve.Affine.CoordinateRing.ramificationIdxProj` : the factor by which the
  projective divisor is multiplied — `e(w | w.under)` at an affine point and `1` at infinity.

## Main statements

**The four hypothesis classes, written out per declaration over all 13 declarations of this file**
(13 public, none private).  ⚠️ It is a complete account of those four and not of every binder.
⚠️ **The population is the 13 SOURCE-LEVEL declarations, and a re-implementer sweeping the
environment will get a different number**: the module carries **16** constants, the other three
being `projUnder._proof_1`, `_proof_2` and `_proof_3`, and `_proof_1` has `[W.IsElliptic]` in its
own type — so the first count below reads **11** over all 16 and **10** over the 13.

* `[W.IsElliptic]`: carried by **10** — the two definitions `projUnder` and `ramificationIdxProj`,
  their four `simp` lemmas `projUnder_none`, `projUnder_some`, `ramificationIdxProj_none` and
  `ramificationIdxProj_some`, and the four transport statements
  `divisorProj_functionFieldMap_apply_none`, `divisorProj_functionFieldMap`,
  `divisorProj_functionFieldMap_under_apply_some` and `divisorProj_functionFieldMap_under`.  It is
  where `[IsDedekindDomain W.CoordinateRing]`, and hence `ProjPoint` and `divisorProj`, come from.
  ⚠️ **The other three carry no curve hypothesis at all**: `norm_map`, `deg_map` and
  `ordInfty_functionFieldMap`.  `norm_map` carries no field hypothesis either — it is two
  commutative rings and a map.
* `[Module.Finite F K]`: carried by **8** — the two definitions, their four `simp` lemmas, and the
  two `under`-forms `divisorProj_functionFieldMap_under_apply_some` and
  `divisorProj_functionFieldMap_under`.  It is what makes `HeightOneSpectrum.under` total, through
  `DivisorBaseChange`'s `instIsIntegralCoordinateRingMap`.  ⚠️ **`divisorProj_functionFieldMap`
  and `divisorProj_functionFieldMap_apply_none` do not carry it**: the first names its `v` and the
  second is at infinity, where there is no fibre to take.
* `[w.asIdeal.LiesOver v.asIdeal]`: carried by **1**, `divisorProj_functionFieldMap`, the only
  statement that names a `v`.
* `g ≠ 0`: carried by **3** — `divisorProj_functionFieldMap`,
  `divisorProj_functionFieldMap_under_apply_some` and `divisorProj_functionFieldMap_under`, i.e.
  every statement whose value at an affine closed point is in play.  ⚠️ **The two statements at
  infinity — `ordInfty_functionFieldMap` and `divisorProj_functionFieldMap_apply_none` — carry no
  hypothesis on `g`** and are true at `g = 0`, where both sides are the junk value `0`.

⚠️ **Every figure in this section was measured on the elaborated types with
`ConstantInfo.type.getUsedConstants`, and the source text cannot decide it.**  ⚠️ **No declaration
below writes `[W.IsElliptic]` in its own signature**: all ten inherit it from the single `variable`
line above `projUnder`.  Of those ten, eight write `[Module.Finite F K]` and nothing else, one —
`divisorProj_functionFieldMap` — writes only `[w.asIdeal.LiesOver v.asIdeal]`, and one —
`divisorProj_functionFieldMap_apply_none` — writes no instance binder of its own at all.  `grep`
reads that file as though `[W.IsElliptic]` were carried by nobody.

* `WeierstrassCurve.Affine.CoordinateRing.norm_map` : `Algebra.norm` commutes with
  `CoordinateRing.map`, over any pair of commutative rings.  **No curve hypothesis and no field
  hypothesis; upstreamable as it stands.**
* `WeierstrassCurve.Affine.CoordinateRing.deg_map` : `deg` is unchanged by base change along a
  homomorphism of fields.
* `WeierstrassCurve.Affine.CoordinateRing.ordInfty_functionFieldMap` : `ordInfty` is unchanged by
  base change, at every `g` and with no hypothesis.
* `WeierstrassCurve.Affine.CoordinateRing.divisorProj_functionFieldMap` and
  `..._under_apply_some` : the affine coordinate of the projective divisor, in the `LiesOver` form
  and in the `under` form.
* `WeierstrassCurve.Affine.CoordinateRing.divisorProj_functionFieldMap_under` : the whole divisor,
  `divisorProj (functionFieldMap g) p = e(p) * divisorProj g (projUnder p)`, with `e(p) = 1` at
  infinity.

## What is *not* here

* **A formula for the affine ramification index.**  Unchanged from `DivisorBaseChange`:
  `ramificationIdx'` is left abstract at an affine point, and ⚠️ **nothing below says it is `1`
  there.**  What is new is that it *is* `1` at infinity, which is `ordInfty_functionFieldMap` and
  is proved rather than assumed.
* **Surjectivity of `projUnder`.**  That every point of the projective curve over `F` has a point
  above it is not stated below; `projUnder` is a map in one direction and the statements are
  quantified over the points of the base-changed curve.  Below the module block the token
  `Surjective` does not occur.
* **A degree statement.**  `degProj` and `degProjPt` do not occur below the module block, so
  nothing here says what base change does to the degree of a divisor or to the degree of a point —
  the residue degree, which is the other half of `e · f = n`.
* **The `Point.map` bridge.**  `#692`'s item 3 is about `Point`, not about `divisor`, and is
  untouched: no statement below has a `W.Point` in it.
* **Anything about `divisorProj` of a specific function.**  The tokens `genX`, `genY` and
  `XClass` do not occur below the module block.

## References

Silverman, *The Arithmetic of Elliptic Curves*, II.3 (divisors, and the degree of a divisor) and
II.2; the unramifiedness of a constant field extension is the function-field form of the statement
that a separable base change is étale.
-/

open Polynomial IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped Polynomial.Bivariate nonZeroDivisors

namespace WeierstrassCurve.Affine.CoordinateRing

/-! ## The norm and the degree under base change -/

variable {R S : Type*} [CommRing R] [CommRing S] {W' : Affine R}

/-- **The algebra norm commutes with coordinate-ring base change.**  Both sides are the explicit
polynomial `Mathlib`'s `norm_smul_basis` computes from the two basis coordinates and the `aᵢ`, one
over `R[X]` and one over `S[X]`, and `Polynomial.map` is a ring homomorphism carrying one to the
other.

No curve hypothesis, no field hypothesis and no injectivity: this is two commutative rings and a
map between them. -/
theorem norm_map (f : R →+* S) (a : W'.CoordinateRing) :
    Algebra.norm S[X] (CoordinateRing.map W' f a) = (Algebra.norm R[X] a).map f := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq a
  rw [map_add, CoordinateRing.map_smul, CoordinateRing.map_smul, map_one, CoordinateRing.map_mk,
    Polynomial.map_X, norm_smul_basis, norm_smul_basis]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_add, Polynomial.map_C, Polynomial.map_X]

variable {F : Type*} [Field F] {W : Affine F} {K : Type*} [Field K]

/-- **Base change does not change `deg`.**  `deg` is the `natDegree` of the norm, the norm
base-changes by `norm_map`, and `Polynomial.map` along a homomorphism of fields is injective and
therefore preserves `natDegree`. -/
theorem deg_map (f : F →+* K) (a : W.CoordinateRing) :
    deg (W.map f) (CoordinateRing.map W f a) = deg W a := by
  rw [deg, deg, norm_map, Polynomial.natDegree_map]

/-! ## The order at infinity -/

variable (W) (K) [Algebra F K]

/-- **The order at infinity is preserved exactly by base change**, with no ramification index and
no hypothesis on `g` — including `g = 0`, where both sides are the junk value `0`.

⚠️ **This is the statement that the place at infinity is unramified in a constant field
extension.**  Contrast `ord_functionFieldMap`, where an affine order is multiplied by
`e(w | v)` and nothing in this development says that index is `1`.  The two behave differently
because `ordInfty` is computed from `deg` rather than read off a factorisation: writing `g = a / b`
with `a b : F[W]` gives `ordInfty g = deg b - deg a`, and `deg_map` says both degrees survive the
base change unchanged. -/
theorem ordInfty_functionFieldMap (g : W.FunctionField) :
    ordInfty (W.map (algebraMap F K)) (functionFieldMap W K g) = ordInfty W g := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [map_zero, ordInfty_zero, ordInfty_zero]
  · have hspec : g * genPsi W ((IsLocalization.sec W.CoordinateRing⁰ g).2 : W.CoordinateRing)
        = genPsi W (IsLocalization.sec W.CoordinateRing⁰ g).1 := IsLocalization.sec_spec _ g
    have hb0 : ((IsLocalization.sec W.CoordinateRing⁰ g).2 : W.CoordinateRing) ≠ 0 :=
      nonZeroDivisors.coe_ne_zero _
    have hmapb : CoordinateRing.map W (algebraMap F K)
        ((IsLocalization.sec W.CoordinateRing⁰ g).2 : W.CoordinateRing) ≠ 0 := fun h =>
      hb0 (CoordinateRing.map_injective (algebraMap F K).injective (by rw [h, map_zero]))
    have hg' : functionFieldMap W K g ≠ 0 := fun h =>
      hg (functionFieldMap_injective W K (by rw [h, map_zero]))
    have hmap : functionFieldMap W K g * genPsi (W.map (algebraMap F K))
          (CoordinateRing.map W (algebraMap F K)
            ((IsLocalization.sec W.CoordinateRing⁰ g).2 : W.CoordinateRing))
        = genPsi (W.map (algebraMap F K))
          (CoordinateRing.map W (algebraMap F K) (IsLocalization.sec W.CoordinateRing⁰ g).1) := by
      rw [← functionFieldMap_algebraMap, ← functionFieldMap_algebraMap, ← map_mul, hspec]
    rw [ordInfty_eq_sub hg' hmapb hmap, ordInfty_eq_sub hg hb0 hspec, deg_map, deg_map]

/-! ## The projective divisor -/

variable [W.IsElliptic]

/-- **The base-change map on the points of the projective curve.**  An affine closed point of
`W⁄K` goes to the closed point of `W` it lies over, and the point at infinity goes to the point at
infinity.  It is `HeightOneSpectrum.under` with the infinite place carried along, which is what
makes `divisorProj` transport in one statement. -/
noncomputable def projUnder [Module.Finite F K] (p : ProjPoint (W.map (algebraMap F K))) :
    ProjPoint W :=
  p.map (HeightOneSpectrum.under W.CoordinateRing)

/-- **The ramification index of a point of the projective curve over its image**: `e(w | w.under)`
at an affine closed point, and `1` at the point at infinity — where it is not an assumption but
`ordInfty_functionFieldMap`. -/
noncomputable def ramificationIdxProj [Module.Finite F K]
    (p : ProjPoint (W.map (algebraMap F K))) : ℕ :=
  p.elim 1 fun w =>
    (HeightOneSpectrum.under W.CoordinateRing w).asIdeal.ramificationIdx' w.asIdeal

@[simp]
theorem projUnder_none [Module.Finite F K] : projUnder W K none = none := rfl

@[simp]
theorem projUnder_some [Module.Finite F K]
    (w : HeightOneSpectrum (W.map (algebraMap F K)).CoordinateRing) :
    projUnder W K (some w) = some (HeightOneSpectrum.under W.CoordinateRing w) := rfl

@[simp]
theorem ramificationIdxProj_none [Module.Finite F K] : ramificationIdxProj W K none = 1 := rfl

@[simp]
theorem ramificationIdxProj_some [Module.Finite F K]
    (w : HeightOneSpectrum (W.map (algebraMap F K)).CoordinateRing) :
    ramificationIdxProj W K (some w)
      = (HeightOneSpectrum.under W.CoordinateRing w).asIdeal.ramificationIdx' w.asIdeal := rfl

/-- **The projective divisor at infinity transports with no factor**, and with no hypothesis on
`g`.

⚠️ **Not a `simp` lemma, and that is measured rather than chosen**: `divisorProj_apply_none` is
itself `simp`, so this left-hand side is not in simp-normal form and Mathlib's `simpNF` linter
rejects the attribute.  The content is `ordInfty_functionFieldMap`; this is the reading of it on
`divisorProj`, kept because it is the coordinate the assembly below needs by name. -/
theorem divisorProj_functionFieldMap_apply_none (g : W.FunctionField) :
    divisorProj (W.map (algebraMap F K)) (functionFieldMap W K g) none = divisorProj W g none := by
  rw [divisorProj_apply_none, divisorProj_apply_none, ordInfty_functionFieldMap]

variable {W K}

/-- **The projective divisor at an affine closed point `w` lying over `v`**, for a nonzero `g`: the
affine coordinate of `divisorProj`, multiplied by the ramification index exactly as `divisor` is in
`divisor_functionFieldMap`. -/
theorem divisorProj_functionFieldMap (v : HeightOneSpectrum W.CoordinateRing)
    (w : HeightOneSpectrum (W.map (algebraMap F K)).CoordinateRing)
    [w.asIdeal.LiesOver v.asIdeal] {g : W.FunctionField} (hg : g ≠ 0) :
    divisorProj (W.map (algebraMap F K)) (functionFieldMap W K g) (some w)
      = (v.asIdeal.ramificationIdx' w.asIdeal : ℤ) * divisorProj W g (some v) := by
  rw [divisorProj_apply_some, divisorProj_apply_some]
  exact ord_functionFieldMap W K v w hg

/-- **The projective divisor at an affine closed point, quantified over `w` alone**, for a finite
extension `K / F` and a nonzero `g`. -/
theorem divisorProj_functionFieldMap_under_apply_some [Module.Finite F K]
    (w : HeightOneSpectrum (W.map (algebraMap F K)).CoordinateRing)
    {g : W.FunctionField} (hg : g ≠ 0) :
    divisorProj (W.map (algebraMap F K)) (functionFieldMap W K g) (some w)
      = (ramificationIdxProj W K (some w) : ℤ)
          * divisorProj W g (projUnder W K (some w)) := by
  rw [projUnder_some, ramificationIdxProj_some, divisorProj_apply_some, divisorProj_apply_some]
  exact ord_functionFieldMap_under W K w hg

/-- **The projective divisor transports, at every point of the projective curve at once**, for a
finite extension `K / F` and a nonzero `g`:
`divisorProj (functionFieldMap g) p = e(p) * divisorProj g (projUnder p)`.

⚠️ **The two cases are not the same statement with a different constant.**  At an affine point the
factor is a ramification index this development leaves abstract; at infinity it is `1`, and that is
`ordInfty_functionFieldMap` rather than a convention chosen to make the formula uniform. -/
theorem divisorProj_functionFieldMap_under [Module.Finite F K]
    (p : ProjPoint (W.map (algebraMap F K))) {g : W.FunctionField} (hg : g ≠ 0) :
    divisorProj (W.map (algebraMap F K)) (functionFieldMap W K g) p
      = (ramificationIdxProj W K p : ℤ) * divisorProj W g (projUnder W K p) := by
  cases p with
  | none => rw [projUnder_none, ramificationIdxProj_none]; simpa using
      divisorProj_functionFieldMap_apply_none W K g
  | some w => exact divisorProj_functionFieldMap_under_apply_some w hg

end WeierstrassCurve.Affine.CoordinateRing
