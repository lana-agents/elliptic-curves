/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.DivisorBaseChange

/-!
# Base change at the closed point of a rational point: the ramification index is `1`

`EllipticCurves.FunctionField.DivisorBaseChange` transports `ord` and `divisor` along
`functionFieldMap W K`, with a ramification index in front, and its `## What is *not* here`
records that nothing in it computes that index:

> **A formula for the ramification index.**  `ramificationIdx'` is left abstract.  In particular
> ⚠️ **nothing below says it is `1`**, which is what a separable `K / F` would give, and which is
> what a consumer wanting `divisor` to transport *on the nose* needs.

⚠️ **That bullet is a claim about that file and it stays true; nothing here edits it.**  This file
computes the index at **one** family of closed points — those cut out by a point `(x, y)` of `W(F)`
that is already rational over the base — and there the answer is `1`, the fibre is a singleton, and
`ord` transports with no factor at all.  Away from that family nothing below says anything, and the
general statement is not proved anywhere in this tree.

## The mechanism, and why it is not the residue-field argument

The reason usually given is that the residue field at the base-changed point is `K`, so that
`f = [K : F]` and `Σ e_i f_i = [K(W⁄K) : F(W)]` force `e = 1` and one point in the fibre.
⚠️ **That is Mathlib's `Ideal.sum_ramification_inertia`, whose `IsIntegralClosure` hypothesis is
nowhere discharged for `F[W] → K[W⁄K]` in this tree, and none of it is needed.**  The whole
content is one ideal identity:

```
Ideal.map (algebraMap F[W] K[W⁄K]) (XYIdeal W x (C y)) = XYIdeal (W⁄K) (x : K) (C (y : K))
```

`map_asIdeal_pointClosedPoint` below.  It holds because `CoordinateRing.map` sends `XClass` to
`XClass` and `YClass` to `YClass` and `Ideal.map_span` carries a two-element span across.  Given it:

* the index is `Ideal.ramificationIdx'_map_self_eq_one`, whose two hypotheses are `map p ≠ ⊤` and
  `map p ≠ ⊥` — and both are read off `XYIdeal_isMaximal` and `XYIdeal_ne_bot` **over `K`**, which
  `EllipticCurves.FunctionField.PointClosedPoint` already proves over every field;
* `LiesOver` is maximality of the base ideal against `Ideal.le_comap_map`: the contraction is a
  proper ideal containing a maximal one, so it is that one;
* the fibre is a singleton for the same reason one level up: a closed point over `v` contains
  `Ideal.map v`, which is maximal over `K`, and is itself proper.

⚠️ **No counting, no separability, no integral closure**, and — for the ideal identity, the
`LiesOver` instance and the singleton — **no `[W.IsElliptic]` and no Dedekind hypothesis of any
kind**: `HeightOneSpectrum` is `@[nolint unusedArguments]` in its Dedekind instance, so
`pointClosedPoint` carries none and those three inherit it.  The index statement is where
`[W.IsElliptic]` **first** enters, because `ramificationIdx'_map_self_eq_one` wants
`[IsDedekindDomain K[W⁄K]]`; the two transports and `divisor_functionFieldMap_eq_single` take it
after that, so **four** of the fifteen public declarations bind it and `## Main statements` below
names them.

## Where this is consumed

`#2029` is the `n = 2` `hprin` assembly, and its step 5 is the only step it leaves unpriced: a
hypothesis `divisor W f = Finsupp.single (pointClosedPoint h) 2` has to be carried up to `K`, and
transported naively it becomes `∑_{w ∣ v} 2 · e_w · w`, which is a `single … 2` only if the fibre is
a singleton and `e = 1` there.  `divisor_functionFieldMap_eq_single` below is that step, at a
general coefficient `n : ℤ` because the proof does not look at the coefficient.

## Main definitions

* `WeierstrassCurve.Affine.CoordinateRing.pointClosedPointBaseChange` : the closed point of `W⁄K`
  cut out by the same rational point `(x, y)`.  ⚠️ A `def` rather than a local abbreviation because
  `pointClosedPoint`'s base field is its own `F`: the base-changed point cannot be named by
  instantiating that argument, and every statement below would otherwise be written out in full.
  It binds neither `[W.IsElliptic]` nor any Dedekind instance, for the reason given above.

## Main statements

**The hypotheses the bullets below omit.**  `map_XClass`, `map_YClass` and `map_XYIdeal` are stated
over two arbitrary commutative rings and a `→+*` between them, and mention no curve over a field at
all.  Every other statement below takes a field extension `K / F` and a point `(x, y)` with
`h : W.Equation x y`, and beyond that: `ramificationIdx'_pointClosedPointBaseChange`,
`ord_functionFieldMap_pointClosedPointBaseChange`,
`divisor_functionFieldMap_pointClosedPointBaseChange` and `divisor_functionFieldMap_eq_single` take
`[W.IsElliptic]`; `under_pointClosedPointBaseChange`, `under_eq_iff_liesOver` and
`divisor_functionFieldMap_eq_single` take `[Module.Finite F K]`; the two `ord` / `divisor`
transports and `divisor_functionFieldMap_eq_single` take `f ≠ 0`; and
`eq_pointClosedPointBaseChange_of_liesOver` takes the `LiesOver` hypothesis its name records.
⚠️ `pointClosedPointBaseChange_asIdeal`, `isMaximal_asIdeal_pointClosedPointBaseChange`,
`map_asIdeal_pointClosedPoint`, `liesOver_pointClosedPointBaseChange` and
`eq_pointClosedPointBaseChange_of_liesOver` take **neither** `[W.IsElliptic]` nor
`[Module.Finite F K]`.

* `WeierstrassCurve.Affine.CoordinateRing.map_XClass`, `map_YClass` and `map_XYIdeal` :
  `CoordinateRing.map W' f` on the generators of `XYIdeal`, and on the ideal they span.  **No curve
  over a field is mentioned and these are upstreamable beside `CoordinateRing.map_mk` as they
  stand.**
* `WeierstrassCurve.Affine.CoordinateRing.map_asIdeal_pointClosedPoint` : the base-changed closed
  point's ideal is the **extension** of the base one.  Everything else in the file is read off this.
* `WeierstrassCurve.Affine.CoordinateRing.liesOver_pointClosedPointBaseChange` : an `instance`, so
  the `DivisorBaseChange` transports apply at these two points with no `haveI` at the call site.
* `WeierstrassCurve.Affine.CoordinateRing.ramificationIdx'_pointClosedPointBaseChange` : the index
  is `1`.
* `WeierstrassCurve.Affine.CoordinateRing.eq_pointClosedPointBaseChange_of_liesOver` : the fibre
  over the closed point of a rational point is a **singleton**.
* `WeierstrassCurve.Affine.CoordinateRing.ord_functionFieldMap_pointClosedPointBaseChange` and
  `divisor_functionFieldMap_pointClosedPointBaseChange` : the transport **on the nose**, with no
  factor.
* `WeierstrassCurve.Affine.CoordinateRing.under_pointClosedPointBaseChange` and
  `under_eq_iff_liesOver` : the `HeightOneSpectrum.under` forms, which is where finiteness of
  `K / F` enters — `under` is total only because `K[W⁄K]` is integral over `F[W]`.
* `WeierstrassCurve.Affine.CoordinateRing.divisor_functionFieldMap_eq_single` : a divisor that is
  `n` times the closed point of a rational point base-changes to `n` times the base-changed closed
  point, **as a `Finsupp` over the whole spectrum of `K[W⁄K]` and not only at that one point**.

## What is *not* here

* **The index at any other closed point.**  Nothing below is stated at a `v` that is not
  `pointClosedPoint h` for a point of `W(F)`, and the general claim — that `e = 1` for a separable
  `K / F` — is proved nowhere in this tree.  `DivisorBaseChange`'s bullet saying so is **still
  true of that file** and is deliberately not edited.
* **The residue degree.**  `f(w ∣ v)` is `[K : F]` at this point, not `1`, and no statement below
  mentions `inertiaDeg` or a residue field.  ⚠️ A reader who has seen the phrase *"so `e = f = 1`"*
  should read it as `e = 1` and `f = [K : F]`: `f = 1` here would say `K = F`.
* **The fibre's cardinality as a `Fintype` count.**  `eq_pointClosedPointBaseChange_of_liesOver` is
  a uniqueness statement about closed points given a `LiesOver` instance; no `primesOver` set and no
  `Finset.card` occurs below.
* **`divisorProj` and the point at infinity.**  Only the affine `divisor` appears; the tokens
  `divisorProj`, `ProjPoint` and `ordInfty` do not occur below the module block.
* **A discharge of `hprin`, and `#962`.**  This file supplies one row of `#2029`'s twelve-step
  table and nothing below mentions `mulByTwoEndo`, `exists_gS_two` or a principal divisor.
* **`n = 3`.**  Nothing below is stated at an index at all: the coefficient in
  `divisor_functionFieldMap_eq_single` is an arbitrary `n : ℤ` and is not a torsion order.

## Non-vacuity

The `Nonvacuity` section certifies at `EllipticCurves.Fixture.y2EqX3SubX` over `ℚ`, at the rational
point `(0, 0)`, over `(X ^ 2 + 1 : ℚ[X]).SplittingField`, that the index **is** `1` and that `ord`
transports with no factor.  ⚠️ **The extension has to be proper or the certificate is empty**: over
an algebraically closed base, or along an isomorphism, every ramification index is `1` already and
the theorem certifies nothing it did not have.  `certRoot_not_mem_range` is that properness.

⚠️ **This is the certificate `DivisorBaseChange` could not write.**  Its `Nonvacuity` section stands
at exactly this point — the same curve, the same extension, the same rational point — and states the
transport with `ramificationIdx'` left **abstract**, because at that file nothing computes it.
**All five** private declarations rebuilding `certRoot` here are copies rather than citations, for
the ordinary reason: every certificate in that section is `private`, so none of them can be named
from another module.  ⚠️ **Four of them were copies when this branch was written and the fifth
became one while it was in review.**  `equation_zero_zero_base` is the equation of the point over
the **base**, as against that file's `equation_zero_zero_cert`, which is the point over the
**extension**; it was new here at `3f61ad7`, and `02a1652` — PR #770, for its own fibre certificate
at the same base point — landed a byte-identical one in that same section.  Two files needing the
same base-field equation within a day is the base-vs-extension distinction being load-bearing
rather than incidental, and it is the distinction every theorem in this file turns on.
The `Nonvacuity` section below names the five.

## References

Silverman, *The Arithmetic of Elliptic Curves*, II.2 (maps of curves and ramification) and II.3
(divisors).
-/

open Polynomial IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine.CoordinateRing

/-! ## The generators of `XYIdeal` under base change

⚠️ No curve over a field and no Dedekind hypothesis appears in this section: the three statements
are about Mathlib's `CoordinateRing.map` over two commutative rings, and are what
`map_asIdeal_pointClosedPoint` below is assembled from. -/

section Generators

variable {R S : Type*} [CommRing R] [CommRing S] {W' : Affine R} (f : R →+* S)

/-- `CoordinateRing.map` sends the class of `X - x` to the class of `X - f x`. -/
lemma map_XClass (x : R) : map W' f (XClass W' x) = XClass (W'.map f) (f x) := by
  rw [XClass, map_mk, XClass]
  simp

/-- `CoordinateRing.map` sends the class of `Y - y(X)` to the class of `Y - (f ∘ y)(X)`. -/
lemma map_YClass (y : R[X]) : map W' f (YClass W' y) = YClass (W'.map f) (y.map f) := by
  rw [YClass, map_mk, YClass]
  simp

/-- **The extension of `⟨X - x, Y - y(X)⟩` along `CoordinateRing.map` is `⟨X - f x, Y - f y(X)⟩`.**
`Ideal.map_span` moves the two-element span across and the two lemmas above identify the images of
its generators. -/
lemma map_XYIdeal (x : R) (y : R[X]) :
    Ideal.map (map W' f) (XYIdeal W' x y) = XYIdeal (W'.map f) (f x) (y.map f) := by
  rw [XYIdeal, Ideal.map_span, XYIdeal, Set.image_pair, map_XClass, map_YClass]

end Generators

/-! ## The closed point of a rational point, base changed -/

section Point

variable {F : Type*} [Field F] {W : Affine F} (K : Type*) [Field K] [Algebra F K]
  [W.IsElliptic] {x y : F}

/-- **The closed point of `W⁄K` cut out by the same rational point `(x, y)`.**

⚠️ A `def` and not a local notation: `pointClosedPoint`'s base field is its own `F`, so this point
cannot be named by instantiating an argument of it, and every statement below would otherwise carry
`pointClosedPoint (h.map (algebraMap F K))` in full. -/
noncomputable def pointClosedPointBaseChange (h : W.Equation x y) :
    HeightOneSpectrum (W.map (algebraMap F K)).CoordinateRing :=
  pointClosedPoint (h.map (algebraMap F K))

omit [W.IsElliptic] in
@[simp]
theorem pointClosedPointBaseChange_asIdeal (h : W.Equation x y) :
    (pointClosedPointBaseChange K h).asIdeal
      = XYIdeal (W.map (algebraMap F K)) (algebraMap F K x) (C (algebraMap F K y)) :=
  rfl

omit [W.IsElliptic] in
/-- The base-changed closed point is **maximal**, which is what both the index and the singleton
statement below are read off. -/
theorem isMaximal_asIdeal_pointClosedPointBaseChange (h : W.Equation x y) :
    (pointClosedPointBaseChange K h).asIdeal.IsMaximal :=
  XYIdeal_isMaximal (h.map (algebraMap F K))

omit [W.IsElliptic] in
/-- **The base-changed closed point's ideal is the extension of the base one.**  This is the whole
content of the file: `map_XYIdeal` at `algebraMap F K`, with `Polynomial.map_C` identifying the
constant `y`. -/
theorem map_asIdeal_pointClosedPoint (h : W.Equation x y) :
    Ideal.map (algebraMap W.CoordinateRing (W.map (algebraMap F K)).CoordinateRing)
        (pointClosedPoint h).asIdeal
      = (pointClosedPointBaseChange K h).asIdeal := by
  rw [pointClosedPoint_asIdeal, pointClosedPointBaseChange_asIdeal]
  change Ideal.map (CoordinateRing.map W (algebraMap F K)) _ = _
  rw [map_XYIdeal]
  simp

omit [W.IsElliptic] in
/-- **The base-changed closed point lies over the original one.**  An `instance`, so that the
transports of `EllipticCurves.FunctionField.DivisorBaseChange` apply at this pair of points with no
`haveI` at the call site.

The contraction contains the base ideal (`Ideal.le_comap_map`) and is proper, because it is the
contraction of a prime; the base ideal is maximal, so the two are equal. -/
instance liesOver_pointClosedPointBaseChange (h : W.Equation x y) :
    (pointClosedPointBaseChange K h).asIdeal.LiesOver (pointClosedPoint h).asIdeal where
  over := by
    refine (XYIdeal_isMaximal h).eq_of_le
      ((pointClosedPointBaseChange K h).isPrime.comap _).ne_top ?_
    rw [← map_asIdeal_pointClosedPoint K h, Ideal.under_def]
    exact Ideal.le_comap_map

/-- **The ramification index at the closed point of a rational point is `1`**, over any field
extension `K / F` whatever.

`Ideal.ramificationIdx'_map_self_eq_one` computes the index of an extended ideal over itself from
`map p ≠ ⊤` and `map p ≠ ⊥` alone, and `map_asIdeal_pointClosedPoint` says the point here **is** the
extended ideal; maximality and `ne_bot` of a `HeightOneSpectrum` supply the two hypotheses.

⚠️ This is where `[W.IsElliptic]` first enters the file — not for the curve but for
`[IsDedekindDomain K[W⁄K]]`, which that Mathlib lemma binds. -/
theorem ramificationIdx'_pointClosedPointBaseChange (h : W.Equation x y) :
    (pointClosedPoint h).asIdeal.ramificationIdx'
        (pointClosedPointBaseChange K h).asIdeal = 1 := by
  rw [← map_asIdeal_pointClosedPoint K h]
  refine Ideal.ramificationIdx'_map_self_eq_one ?_ ?_ <;>
    rw [map_asIdeal_pointClosedPoint K h]
  · exact (isMaximal_asIdeal_pointClosedPointBaseChange K h).ne_top
  · exact (pointClosedPointBaseChange K h).ne_bot

omit [W.IsElliptic] in
/-- **The fibre over the closed point of a rational point is a singleton.**  A closed point of
`W⁄K` lying over it contains the extended ideal, which is maximal, and is itself proper. -/
theorem eq_pointClosedPointBaseChange_of_liesOver (h : W.Equation x y)
    (w : HeightOneSpectrum (W.map (algebraMap F K)).CoordinateRing)
    [w.asIdeal.LiesOver (pointClosedPoint h).asIdeal] :
    w = pointClosedPointBaseChange K h := by
  have hle : (pointClosedPointBaseChange K h).asIdeal ≤ w.asIdeal := by
    rw [← map_asIdeal_pointClosedPoint K h, Ideal.map_le_iff_le_comap, ← Ideal.under_def]
    exact le_of_eq (Ideal.LiesOver.over ..)
  exact HeightOneSpectrum.ext
    ((isMaximal_asIdeal_pointClosedPointBaseChange K h).eq_of_le w.isPrime.ne_top hle).symm

/-! ## The transport, on the nose

⚠️ Neither statement in this section takes `[Module.Finite F K]`: both go through
`ord_functionFieldMap`, which is quantified over a `(v, w)` pair with a `LiesOver` instance, and not
through the `under`-forms, which are the ones that need integrality. -/

/-- **`ord` transports with no factor at the closed point of a rational point**, which is what
`DivisorBaseChange`'s `ord_functionFieldMap` cannot say at a general pair of points. -/
theorem ord_functionFieldMap_pointClosedPointBaseChange (h : W.Equation x y)
    {f : W.FunctionField} (hf : f ≠ 0) :
    ord (pointClosedPointBaseChange K h) (functionFieldMap W K f) = ord (pointClosedPoint h) f := by
  rw [ord_functionFieldMap W K (pointClosedPoint h) _ hf,
    ramificationIdx'_pointClosedPointBaseChange K h]
  simp

/-- **The `divisor` form of `ord_functionFieldMap_pointClosedPointBaseChange`**, read at the one
point.  The statement over the whole spectrum is `divisor_functionFieldMap_eq_single`. -/
theorem divisor_functionFieldMap_pointClosedPointBaseChange (h : W.Equation x y)
    {f : W.FunctionField} (hf : f ≠ 0) :
    divisor (W.map (algebraMap F K)) (functionFieldMap W K f) (pointClosedPointBaseChange K h)
      = divisor W f (pointClosedPoint h) := by
  simpa only [divisor_apply] using ord_functionFieldMap_pointClosedPointBaseChange K h hf

/-! ## The `under`-forms, for a finite extension

`HeightOneSpectrum.under` is total only because `K[W⁄K]` is integral over `F[W]`, which
`DivisorBaseChange`'s `instIsIntegralCoordinateRingMap` supplies for `[Module.Finite F K]`.  That is
the only reason finiteness appears in this file. -/

omit [W.IsElliptic] in
/-- **The base-changed closed point contracts to the original one.** -/
theorem under_pointClosedPointBaseChange [Module.Finite F K] (h : W.Equation x y) :
    HeightOneSpectrum.under W.CoordinateRing (pointClosedPointBaseChange K h)
      = pointClosedPoint h := by
  refine HeightOneSpectrum.ext ?_
  rw [HeightOneSpectrum.under_asIdeal]
  exact (Ideal.LiesOver.over ..).symm

omit [W.IsElliptic] in
/-- **Contracting to the closed point of a rational point is the same as lying over it.**  This is
what turns the `under`-form of a transport into the `LiesOver`-form the section above is stated in,
and it is the case split `divisor_functionFieldMap_eq_single` runs on. -/
theorem under_eq_iff_liesOver [Module.Finite F K] (h : W.Equation x y)
    (w : HeightOneSpectrum (W.map (algebraMap F K)).CoordinateRing) :
    HeightOneSpectrum.under W.CoordinateRing w = pointClosedPoint h ↔
      w.asIdeal.LiesOver (pointClosedPoint h).asIdeal := by
  constructor
  · intro hu
    rw [← hu, HeightOneSpectrum.under_asIdeal]
    infer_instance
  · intro hlo
    exact HeightOneSpectrum.ext ((HeightOneSpectrum.under_asIdeal ..).trans hlo.over.symm)

/-- **A divisor supported at the closed point of a rational point base-changes on the nose.**

This is the statement a descent argument takes as its hypothesis: over `K` the transported divisor
is again a `Finsupp.single`, at the base-changed point and with the **same** coefficient.  Both
halves of the file are used — at `w` in the fibre, the fibre is a singleton and the index is `1`; at
any other `w`, its contraction is a different closed point and the base divisor vanishes there.

⚠️ The coefficient is an arbitrary `n : ℤ`: nothing in the proof looks at it, and in particular this
is not a statement about torsion of any order. -/
theorem divisor_functionFieldMap_eq_single [Module.Finite F K] (h : W.Equation x y)
    {f : W.FunctionField} (hf : f ≠ 0) {n : ℤ}
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h) n) :
    divisor (W.map (algebraMap F K)) (functionFieldMap W K f)
      = Finsupp.single (pointClosedPointBaseChange K h) n := by
  ext w
  rw [divisor_functionFieldMap_under W K w hf, hfdiv]
  by_cases hw : HeightOneSpectrum.under W.CoordinateRing w = pointClosedPoint h
  · haveI : w.asIdeal.LiesOver (pointClosedPoint h).asIdeal := (under_eq_iff_liesOver K h w).mp hw
    have hweq : w = pointClosedPointBaseChange K h :=
      eq_pointClosedPointBaseChange_of_liesOver K h w
    subst hweq
    rw [hw, Finsupp.single_eq_same, ramificationIdx'_pointClosedPointBaseChange K h,
      Finsupp.single_eq_same]
    simp
  · have hne : pointClosedPointBaseChange K h ≠ w := by
      rintro rfl
      exact hw (under_pointClosedPointBaseChange K h)
    rw [Finsupp.single_eq_of_ne hw, mul_zero, Finsupp.single_eq_of_ne (Ne.symm hne)]

end Point

/-! ## Non-vacuity -/

section Nonvacuity

open EllipticCurves.Fixture

/-! The certificate curve is `EllipticCurves.Fixture.y2EqX3SubX` at `R = ℚ`, the rational point is
`(0, 0)`, and the certificate extension is `(X ^ 2 + 1 : ℚ[X]).SplittingField`.  ⚠️ **The extension
is proper** — `certRoot_not_mem_range` below — and that is what makes the certificate say anything:
over an algebraically closed base, or along an isomorphism, every ramification index is `1` before
this file is read.

⚠️ **`DivisorBaseChange`'s own `Nonvacuity` section stands at exactly this curve, this extension and
this point, and leaves `ramificationIdx'` abstract**, because nothing in that file computes it.
**Five** of the private declarations below — `certRoot`, `certRoot_eval`,
`certRoot_not_mem_range`, `genPsi_XClass_ne_zero` and `equation_zero_zero_base` — are copies of its
chain rather than citations, for the ordinary reason: they are `private` there and cannot be named
from another module.  ⚠️ **The last of the five was not a copy when it was written.**  That
section's `equation_zero_zero_cert` is the equation over the **extension** and what this file needs
is the same point over the **base** — the whole difference between a rational point and a point of
`W⁄K` — so `equation_zero_zero_base` was new here at `3f61ad7`, and `02a1652` (PR #770) then landed
a byte-identical declaration of the same name in that section, for its own fibre certificate at the
same base point.  ⚠️ **The count is keyed to `02a1652`** and a later commit to that file can move
it; what does not move is the reason none of the five is a citation. -/

/-- A root of `X² + 1` in its splitting field over `ℚ`.

⚠️ Built from `Polynomial.SplittingField.splits` rather than from `IsSplittingField.splits`:
`IsSplittingField ℚ (X² + 1).SplittingField (X² + 1)` is **not** found by typeclass search at this
pin, which is the trap `DivisorBaseChange`'s copy of this definition also records. -/
private noncomputable def certRoot : (X ^ 2 + 1 : ℚ[X]).SplittingField :=
  rootOfSplits (Polynomial.SplittingField.splits (K := ℚ) (f := (X ^ 2 + 1 : ℚ[X])))
    (by rw [Polynomial.degree_map, show (X ^ 2 + 1 : ℚ[X]).degree = 2 by compute_degree!]
        exact two_ne_zero)

private theorem certRoot_eval :
    ((X ^ 2 + 1 : ℚ[X]).map
      (algebraMap ℚ (X ^ 2 + 1 : ℚ[X]).SplittingField)).eval certRoot = 0 := by
  rw [certRoot]; exact eval_rootOfSplits _ _

/-- **The certificate extension is proper**: `X² + 1` has no rational root, so its root in the
splitting field is outside the image of `ℚ`. -/
private theorem certRoot_not_mem_range :
    certRoot ∉ Set.range (algebraMap ℚ (X ^ 2 + 1 : ℚ[X]).SplittingField) := by
  rintro ⟨q, hq⟩
  have h := certRoot_eval
  rw [← hq, eval_map, Polynomial.eval₂_hom] at h
  have hq0 : (q : ℚ) ^ 2 + 1 = 0 := by
    have := (map_eq_zero (algebraMap ℚ (X ^ 2 + 1 : ℚ[X]).SplittingField)).mp h
    simpa using this
  nlinarith [sq_nonneg (q : ℚ)]

/-- `(0, 0)` is a point of `y² = x³ - x` over the **base** field `ℚ`.  ⚠️ It has to be rational over
the base: a point of the base-changed curve is what this file says nothing about. -/
private theorem equation_zero_zero_base : (y2EqX3SubX ℚ).Equation 0 0 := by
  rw [equation_iff']
  simp [y2EqX3SubX]

/-- **The index is `1`** at the closed point of `(0, 0)` on `y² = x³ - x` over `ℚ`, along the proper
quadratic extension `(X² + 1).SplittingField`. -/
private theorem ramificationIdx'_cert :
    (pointClosedPoint equation_zero_zero_base).asIdeal.ramificationIdx'
        (pointClosedPointBaseChange (X ^ 2 + 1 : ℚ[X]).SplittingField
          equation_zero_zero_base).asIdeal = 1 :=
  ramificationIdx'_pointClosedPointBaseChange _ _

/-- The certificate function `x ∈ ℚ(W)` is nonzero. -/
private theorem genPsi_XClass_ne_zero :
    genPsi (y2EqX3SubX ℚ) (XClass (y2EqX3SubX ℚ) 0) ≠ 0 := by
  rw [ne_eq, ← map_zero (genPsi (y2EqX3SubX ℚ))]
  exact fun h => XClass_ne_zero (W' := y2EqX3SubX ℚ) 0 (IsFractionRing.injective _ _ h)

/-- **The transport with no factor on either side**, at the same curve, extension and point at which
`DivisorBaseChange`'s certificate carries a `ramificationIdx'` it cannot evaluate. -/
private theorem ord_functionFieldMap_cert :
    ord (pointClosedPointBaseChange (X ^ 2 + 1 : ℚ[X]).SplittingField equation_zero_zero_base)
        (functionFieldMap (y2EqX3SubX ℚ) (X ^ 2 + 1 : ℚ[X]).SplittingField
          (genPsi (y2EqX3SubX ℚ) (XClass (y2EqX3SubX ℚ) 0)))
      = ord (pointClosedPoint equation_zero_zero_base)
          (genPsi (y2EqX3SubX ℚ) (XClass (y2EqX3SubX ℚ) 0)) :=
  ord_functionFieldMap_pointClosedPointBaseChange _ _ genPsi_XClass_ne_zero

end Nonvacuity

end WeierstrassCurve.Affine.CoordinateRing
