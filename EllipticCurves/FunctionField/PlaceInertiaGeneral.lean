/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByTwoFibreAffine
import EllipticCurves.FunctionField.PlaceDegreeComparison
import EllipticCurves.FunctionField.PlaceRamificationInertia

/-!
# The inertia compatibility over an arbitrary field, and the uncollapsed fundamental identity

`EllipticCurves.FunctionField.PlaceRamificationInertia` proves the two local compatibilities that
connect this development's ramification data to Mathlib's `Ideal.ramificationIdx` and
`Ideal.inertiaDeg`.  **One of them was stated over an arbitrary field and one was not.**  That
file's `## What is *not* here` recorded the gap in one sentence:

> *"the unconditional `Ideal.inertiaDeg 𝔪 P = residueDegreeTwo h2 p` is **not** proved, and would
> need `B ⧸ P` to be identified with the residue field of the localisation `B_v = placeOf W p` and
> `A ⧸ 𝔪_A` with `κ(q)`, compatibly with the two algebra maps."*

This file is that sentence, discharged.  ⚠️ **The sentence itself is retired in place there**, as a
quotation marked paid and pointing here, so do not expect to find it standing in that file's
`## What is *not* here`; the same is true of the *"is what a later issue owes"* clause on
`sum_ramificationIdxTwo_mul_residueDegreeTwo`.  With it, the fundamental identity

```
∑_{p ↦ q} e_p · f_p = [F(W) : φ F(W)]
```

is available in **this** development's indexing with no hypothesis on `F` beyond the separability
that `#754` already carries — in particular over `ℚ`.

## Why the collapsed form cannot be generalised, and this one can

`sum_toNat_ramificationIdx_fibre` (`PlaceRamificationInertia`) states `∑_{p ↦ q} e_p = finrank`,
with the `f_p` set to `1`.  It carries `[IsAlgClosed F]` and **must**: it runs on
`ideal_inertiaDeg_eq_one`, whose content is that the residue field at *every* place is `F`.  That
is equivalent to the base field being algebraically closed and is false over `ℚ`, where `X² + 1`
names a closed point of degree `2`.  There is no finite extension over which it becomes true.

What generalises is the identity with the `f_p` **kept**.  Nothing else has to change: the
right-hand side `finrank_integralClosure_placeBelow` (`#754`) and the index-set dictionary
`primesOverEquivFibre` (`#755`) are already unconditional, and
`sum_ramificationIdx_mul_inertiaDeg_placeBelow` — Mathlib's identity in Mathlib's indexing — says
of itself that it is *"the form to use over `ℚ`"*.

## The proof, which is the merged ramification half read once more

`ideal_ramificationIdx_eq_toNat` (`PlaceRamificationInertia`) is the ramification compatibility, and
it is already unconditional.  It runs on `#755`'s `placeOf_projPointOfHeightOne`: the place of the
point attached to `v` **is** the localisation `B_v`.  The inertia statement is the residue-field
shadow of that same identification, and it needs no new geometry — only two ring isomorphisms and
the square they sit in:

* `valuationSubringAtPrimeEquivPlace` — `B_v ≃+* placeOf W p`, a `RingEquiv.subringCongr` off
  `placeOf_projPointOfHeightOne`.  Composed with Mathlib's
  `IsLocalization.AtPrime.equivQuotMaximalIdeal` — available because
  `HeightOneSpectrum.valuationSubringAtPrime` carries an `IsLocalization v.asIdeal.primeCompl`
  instance — it gives `B ⧸ P ≃+* κ(p)`;
* `placeComapEquivPlaceBelow` — `placeOf W (comapProjPoint φ p) ≃+* placeBelow φ q`, which is
  `#754`'s `placeBelowEquiv` after transporting along `comapProjPoint φ p = q`.  Through
  `IsLocalRing.ResidueField.mapEquiv` it gives `A ⧸ 𝔪_A ≃+* κ(q)`.

Both `Ideal.inertiaDeg` and `residueDegreeComap` are a `Module.finrank` of the resulting extension,
so `Algebra.finrank_eq_of_equiv_equiv` closes the statement once the square commutes — and it
commutes because both routes send `a` to the residue of the same element of `F(W)`, namely `a`
itself read through `φ.fieldRange ↪ F(W)`.

## Main results

* **`WeierstrassCurve.Affine.ideal_inertiaDeg_eq_residueDegreeComap`** — the inertia compatibility
  over an arbitrary field, `Ideal.inertiaDeg 𝔪_A P = residueDegreeComap φ p`;
* **`WeierstrassCurve.Affine.sum_toNat_ramificationIdx_mul_residueDegreeComap_fibre`** — the
  fundamental identity `∑_{p ↦ q} e_p · f_p = finrank A B` in this development's indexing, with no
  hypothesis on `F`;
* **`sum_ramificationIdxTwo_mul_residueDegreeTwo_of_isSeparable`** (namespace
  `WeierstrassCurve.Affine.CoordinateRing`) and `…_of_charZero` — the `[2]∗` instantiation,
  `∑_{p ↦ q} e_p · f_p = 4`, with separability carried as a hypothesis and discharged over
  `[CharZero F]`;
* `CoordinateRing.residueDegreeProj_projPointOfPoint` and
  `CoordinateRing.residueDegreeTwo_projPointOfPoint`, both in `WeierstrassCurve.Affine` — at an
  `F`-**rational** point the residue degree is `1`, over an arbitrary field.  This is what a
  consumer counting inside the fibre over a rational point uses in place of *"every place is
  rational"*.

## Scope

⚠️ **This does not discharge `hprin` over a general field** (`#962`), and it must not be reported as
doing so.  What it removes is one of the three `[IsAlgClosed F]` inputs to
`exists_nsmul_divisor_eq_divisor_mulByTwoEndo` — the only one that is not a statement about finitely
many algebraic elements being rational.  The other two, `card_torsion_two`
(`EllipticCurves.Torsion.TwoTorsion`) and `exists_nsmul_two_eq`
(`EllipticCurves.Torsion.DoublingSurjective`), are untouched here, as are the Galois-descent step
and Mathlib's Hilbert 90.

⚠️ **Nothing here says `#E[2] = 4`.**  `PlaceRamificationInertia`'s docstring is emphatic about this
and it applies verbatim to the general form: the identity is about total ramification in a fibre,
not about a count of `2`-torsion points.

⚠️ **`[IsAlgClosed F]` is not removed from `residueDegreeProj_eq_one`
(`EllipticCurves.FunctionField.PlaceResidueDegree`) or from `degPt_eq_one`
(`EllipticCurves.FunctionField.PlaceDegreeComparison`), and cannot be** — those are true statements
about algebraically closed base fields whose generalisations are false.  What is available over an
arbitrary field is the *rational-point* case, which is what
`residueDegreeProj_projPointOfPoint` supplies.

⚠️ **`[3]∗` is not instantiated here.**  Everything before the `[2]∗` section is stated for an
arbitrary `φ`, so the mirror is an instantiation; but
`sum_ramificationIdxThree_mul_residueDegreeThree`
(`EllipticCurves.FunctionField.MulByThreeResidueDegree`) is not restated, and `#1046`'s record that
the `n = 3` residue-degree layer was an instantiation rather than a re-derivation is the reason to
price it separately rather than assume it.

⚠️ **The non-vacuity section below certifies that the hypotheses are satisfiable over `ℚ`, and it
does not exhibit a place with `f_p > 1`.**  The statements are strictly stronger than their
`[IsAlgClosed F]` siblings because they *apply* over a field that is not algebraically closed, which
is what the certificate shows; exhibiting a closed point of degree `2` on a specific curve is a
different piece of work and is not attempted.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, III.1.11.
-/

open Module IsLocalRing IsDedekindDomain

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]
  {φ : W.FunctionField →+* W.FunctionField} {q : ProjPoint W}
  (hφF : ∀ c : F, φ (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c)
  (hφint : ∀ z : W.FunctionField, φ.IsIntegralElem z)

section Dedekind

variable [Module.Finite ↥φ.fieldRange W.FunctionField]
  [Algebra.IsSeparable ↥φ.fieldRange W.FunctionField]
  (v : HeightOneSpectrum ↥(integralClosure ↥(placeBelow φ q) W.FunctionField))

/-! ### The two ring isomorphisms

Neither is more than a repackaging: the first transports `#754`'s `placeBelowEquiv` along the fibre
condition, the second is the identity on underlying functions. -/

/-- **The place under `p` is the place below `q`.**  `comapProjPoint φ p = q` holds because `v` lies
over the maximal ideal of `placeBelow φ q`, and `#754`'s `placeBelowEquiv` carries `placeOf W q`
onto `placeBelow φ q`. -/
noncomputable def placeComapEquivPlaceBelow
    [hlies : v.asIdeal.LiesOver (maximalIdeal ↥(placeBelow φ q))] :
    ↥(placeOf W (comapProjPoint hφF hφint (projPointOfHeightOne φ hφF q v)))
      ≃+* ↥(placeBelow φ q) :=
  (RingEquiv.subringCongr (congrArg ValuationSubring.toSubring (congrArg (placeOf W)
    ((comapProjPoint_projPointOfHeightOne_eq_iff hφF hφint v).2 hlies.over.symm)))).trans
    (placeBelowEquiv φ q)

/-- **`B_v` is the place at the point `v` names**, as a ring isomorphism.  This is `#755`'s
`placeOf_projPointOfHeightOne` read through `RingEquiv.subringCongr`; it is the identity on
underlying elements of `F(W)`. -/
noncomputable def valuationSubringAtPrimeEquivPlace :
    ↥(HeightOneSpectrum.valuationSubringAtPrime W.FunctionField v)
      ≃+* ↥(placeOf W (projPointOfHeightOne φ hφF q v)) :=
  RingEquiv.subringCongr
    (congrArg ValuationSubring.toSubring (placeOf_projPointOfHeightOne hφF v).symm)

/-! ### The inertia compatibility -/

set_option maxHeartbeats 1000000 in
-- The two `Ideal.Quotient` types below are large enough that the defeq checks in the commuting
-- square exceed the default budget; nothing in the proof is a search.
/-- **The inertia compatibility, over an arbitrary field.**  Mathlib's inertia degree of `v` over
the place below is this development's relative residue degree of `φ` at the point `v` names.

This is the companion of `ideal_ramificationIdx_eq_toNat` and, unlike `ideal_inertiaDeg_eq_one`, it
assumes nothing about `F`.  The proof is the commuting square of the two isomorphisms above: both
routes send the class of `a` to the residue of `a` itself, read through `φ.fieldRange ↪ F(W)`, and
`Algebra.finrank_eq_of_equiv_equiv` turns that into the equality of the two `finrank`s. -/
theorem ideal_inertiaDeg_eq_residueDegreeComap
    [hlies : v.asIdeal.LiesOver (maximalIdeal ↥(placeBelow φ q))] :
    v.asIdeal.inertiaDeg ↥(placeBelow φ q)
      = residueDegreeComap hφF hφint (projPointOfHeightOne φ hφF q v) := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : (maximalIdeal ↥(placeBelow φ q)).IsMaximal := maximalIdeal.isMaximal _
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal ↥(placeBelow φ q)) v.asIdeal,
    residueDegreeComap]
  refine Algebra.finrank_eq_of_equiv_equiv
    (ResidueField.mapEquiv (placeComapEquivPlaceBelow hφF hφint v)).symm
    ((IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal
        ↥(HeightOneSpectrum.valuationSubringAtPrime W.FunctionField v)).trans
      (ResidueField.mapEquiv (valuationSubringAtPrimeEquivPlace hφF v))) ?_
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
  change residue _ _ = residue _ _
  refine congrArg (residue _) (Subtype.ext ?_)
  rw [RingHom.algebraMap_toAlgebra, coe_placeHomComap]
  have key : φ (((placeComapEquivPlaceBelow hφF hφint v).symm a :
      ↥(placeOf W (comapProjPoint hφF hφint (projPointOfHeightOne φ hφF q v))))
      : W.FunctionField) = ((a : ↥φ.fieldRange) : W.FunctionField) := by
    change φ (φ.rangeRestrictFieldEquiv.symm (a : ↥φ.fieldRange)) = _
    rw [← RingHom.rangeRestrictFieldEquiv_apply_coe, RingEquiv.apply_symm_apply]
  exact key.trans rfl

/-! ### The fundamental identity, uncollapsed -/

include hφF hφint in
/-- **The fundamental identity in this development's indexing, over an arbitrary field**:
`∑_{p ↦ q} e_p · f_p = [F(W) : φ F(W)]` locally at `q`.

Same proof as `sum_toNat_ramificationIdx_fibre`, with `ideal_inertiaDeg_eq_residueDegreeComap` in
place of `ideal_inertiaDeg_eq_one`.  The `f_p` is kept rather than set to `1`, which is the entire
difference and the entire reason this one needs no hypothesis on `F`. -/
theorem sum_toNat_ramificationIdx_mul_residueDegreeComap_fibre :
    ∑ p ∈ (finite_comapProjPoint_preimage_singleton hφF hφint q).toFinset,
        (ramificationIdx hφF hφint p).toNat * residueDegreeComap hφF hφint p
      = finrank ↥(placeBelow φ q) ↥(integralClosure ↥(placeBelow φ q) W.FunctionField) := by
  haveI : Finite ↥((maximalIdeal ↥(placeBelow φ q)).primesOver
      ↥(integralClosure ↥(placeBelow φ q) W.FunctionField)) :=
    finite_primesOver_maximalIdeal_placeBelow hφF hφint
  haveI := Fintype.ofFinite ↥((maximalIdeal ↥(placeBelow φ q)).primesOver
    ↥(integralClosure ↥(placeBelow φ q) W.FunctionField))
  rw [← sum_ramificationIdx_mul_inertiaDeg_placeBelow (φ := φ) (q := q), ← Finset.sum_coe_sort]
  refine Eq.symm (Fintype.sum_equiv ((primesOverEquivFibre hφF hφint).trans
    (Equiv.subtypeEquivRight fun x => (Set.Finite.mem_toFinset _).symm)) _ _ fun P => ?_)
  haveI : (heightOneOfPrimesOver P).asIdeal.LiesOver (maximalIdeal ↥(placeBelow φ q)) := P.2.2
  change (heightOneOfPrimesOver P).asIdeal.ramificationIdx ↥(placeBelow φ q)
      * (heightOneOfPrimesOver P).asIdeal.inertiaDeg ↥(placeBelow φ q) = _
  rw [ideal_inertiaDeg_eq_residueDegreeComap hφF hφint (heightOneOfPrimesOver P),
    ideal_ramificationIdx_eq_toNat hφF hφint (heightOneOfPrimesOver P)]
  rfl

end Dedekind

/-! ### The residue degree at a rational point

Over an algebraically closed base field every place is rational and `residueDegreeProj_eq_one`
applies at all of them.  Over an arbitrary field that is false, but the *rational* points still have
residue degree `1`, and a consumer counting inside the fibre over a rational point needs nothing
more. -/

variable [W.IsElliptic]

open scoped Classical in
/-- **A point of the projective curve coming from an `F`-rational point has residue degree `1`**,
over an arbitrary base field.

At infinity this is the definitional weight of `degProjPt`; at an affine point it is
`degPt_pointClosedPoint` (`EllipticCurves.FunctionField.RationalPointDegree`).  The two degrees are
compared by `degProjPt_eq_residueDegreeProj`, which is itself unconditional. -/
theorem CoordinateRing.residueDegreeProj_projPointOfPoint (S : W.Point) :
    residueDegreeProj W (projPointOfPoint W S) = 1 := by
  rw [← degProjPt_eq_residueDegreeProj]
  cases S with
  | zero => exact degProjPt_none
  | some x y h => exact degPt_pointClosedPoint h

namespace CoordinateRing

open scoped Classical in
/-- **`[2]∗` is residually trivial at a rational point**, over an arbitrary base field.  This is
the input that replaces *"every place is rational"* in a count inside the fibre over a rational
point. -/
theorem residueDegreeTwo_projPointOfPoint (h2 : (2 : F) ≠ 0) (S : W.Point) :
    residueDegreeTwo h2 (projPointOfPoint W S) = 1 :=
  residueDegreeTwo_eq_one_of_residueDegreeProj_eq_one h2 (residueDegreeProj_projPointOfPoint S)

/-! ### The `[2]∗` instantiation -/

/-- **`∑_{p ↦ q} e_p · f_p = 4` for `[2]∗`, over an arbitrary field**, with separability carried as
a hypothesis exactly as `#754` carries it.

⚠️ The separability is **not** discharged here.  Over `F̄` it is
`isSeparable_mulByTwoEndoFieldRange_of_isAlgClosed`, and discharging it inside this statement would
put back the hypothesis the statement exists to remove; over `[CharZero F]` it is
`isSeparable_mulByTwoEndoFieldRange`, and that instantiation is the next declaration. -/
theorem sum_ramificationIdxTwo_mul_residueDegreeTwo_of_isSeparable (h2 : (2 : F) ≠ 0)
    (hsep : Algebra.IsSeparable ↥(mulByTwoEndo (W := W) h2).fieldRange W.FunctionField)
    (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointTwo_preimage_singleton h2 q).toFinset,
      (ramificationIdxTwo h2 p).toNat * residueDegreeTwo h2 p = 4 := by
  haveI := module_finite_mulByTwoEndoFieldRange (W := W) h2
  haveI := hsep
  rw [show (4 : ℕ) = finrank ↥(placeBelowTwo W h2 q)
      ↥(integralClosure ↥(placeBelowTwo W h2 q) W.FunctionField) from
    (finrank_integralClosure_placeBelowTwo h2 hsep q).symm]
  exact sum_toNat_ramificationIdx_mul_residueDegreeComap_fibre
    (mulByTwoEndo_algebraMap_base h2) (mulByTwoEndo_isIntegralElem h2)

/-- **`∑_{p ↦ q} e_p · f_p = 4` for `[2]∗` in characteristic zero.**  This is the form available
over `ℚ`, where the collapsed `sum_ramificationIdxTwo_eq_four` is not.

`[CharZero F]` and `[IsAlgClosed F]` remain incomparable, as `#754` records: neither implies the
other, and this one needs no algebraic closure. -/
theorem sum_ramificationIdxTwo_mul_residueDegreeTwo_of_charZero [CharZero F] (h2 : (2 : F) ≠ 0)
    (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointTwo_preimage_singleton h2 q).toFinset,
      (ramificationIdxTwo h2 p).toNat * residueDegreeTwo h2 p = 4 :=
  sum_ramificationIdxTwo_mul_residueDegreeTwo_of_isSeparable h2
    (isSeparable_mulByTwoEndoFieldRange h2) q

omit [W.IsElliptic] in
/-- **Consistency with the collapsed form.**  Over an algebraically closed base field every place is
rational, so every `f_p` is `1` and this file's identity is
`sum_ramificationIdxTwo_eq_four` (`EllipticCurves.FunctionField.PlaceRamificationInertia`).  Stated
as a check that nothing drifted between the two, not because a consumer wants it. -/
theorem sum_ramificationIdxTwo_mul_residueDegreeTwo_eq_sum_of_isAlgClosed [IsAlgClosed F]
    (h2 : (2 : F) ≠ 0) (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointTwo_preimage_singleton h2 q).toFinset,
        (ramificationIdxTwo h2 p).toNat * residueDegreeTwo h2 p
      = ∑ p ∈ (finite_comapProjPointTwo_preimage_singleton h2 q).toFinset,
        (ramificationIdxTwo h2 p).toNat := by
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [residueDegreeTwo_eq_one_of_residueDegreeProj_eq_one h2 (residueDegreeProj_eq_one p), mul_one]

end CoordinateRing

/-! ### Non-vacuity

⚠️ The point of this file is that its statements apply over a field that is **not** algebraically
closed, so a certificate over `AlgebraicClosure ℚ` would certify the merged statement instead of
this one.  `y² = x³ − x` over `ℚ` supplies `[W.IsElliptic]`, `[CharZero F]` and `(2 : F) ≠ 0` at
once, and is the curve the rest of `FunctionField/` uses.

⚠️ This certificate shows the hypotheses are **satisfiable**, not that some `f_p` exceeds `1`.
Exhibiting a closed point of degree `2` on a named curve is a different piece of work and is not
attempted here; see the module docstring. -/

section Nonvacuity

/-- The curve `y² = x³ − x` over `ℚ`, of discriminant `64`. -/
private noncomputable def exampleCurve : Affine ℚ := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleTwo : (2 : ℚ) ≠ 0 := by norm_num

/-- The identity of this file, instantiated over `ℚ` — a base field that is not algebraically
closed, so `sum_ramificationIdxTwo_eq_four` does not apply to it. -/
private noncomputable example (q : ProjPoint exampleCurve) :
    ∑ p ∈ (CoordinateRing.finite_comapProjPointTwo_preimage_singleton exampleTwo q).toFinset,
      (CoordinateRing.ramificationIdxTwo exampleTwo p).toNat
        * CoordinateRing.residueDegreeTwo exampleTwo p = 4 :=
  CoordinateRing.sum_ramificationIdxTwo_mul_residueDegreeTwo_of_charZero exampleTwo q

end Nonvacuity

end WeierstrassCurve.Affine
