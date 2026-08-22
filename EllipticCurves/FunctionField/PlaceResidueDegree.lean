/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.PlaceResidueField
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The residue field of an affine closed point is the quotient by that point, and is `F` over `F̄`

`EllipticCurves.FunctionField.PlaceResidueField` (`#742`) builds the residue field
`residueFieldProj W p = IsLocalRing.ResidueField (placeOf W p)` of a point of the projective curve,
together with `residueDegreeProj W p = Module.finrank F (residueFieldProj W p)` and the
reformulation

```lean
residueDegreeProj W p = 1 ↔ Function.Surjective (algebraMap F (residueFieldProj W p))
```

This file computes both, **in the affine branch** `p = some v`:

* `residueFieldProjSomeEquiv` — `κ(some v) ≃ₐ[F] F[W] ⧸ v.asIdeal`;
* `Module.Finite F (residueFieldProj W (some v))` — Zariski's lemma, with **no** hypothesis on `F`;
* `residueDegreeProj_some_eq_one` — over an algebraically closed base field, `[κ(some v) : F] = 1`.

## The route, and why the localisation step is the only real work

`placeOf W (some v)` is `HeightOneSpectrum.valuationSubringAtPrime W.FunctionField v`, which
Mathlib knows is a localisation of `F[W]` at `v.asIdeal.primeCompl`, and `v.asIdeal` is maximal
(`IsDedekindDomain.HeightOneSpectrum.isMaximal`).  So the composite

```lean
residueHomSome v : F[W] →ₐ[F] κ(some v)
```

— reduce into the place, then take the residue — has kernel exactly `v.asIdeal`
(`IsLocalization.AtPrime.to_map_mem_maximal_iff`), and is **surjective**: an element of the place
is `a / s` with `s ∉ v.asIdeal`, and `s` is invertible modulo the maximal ideal `v.asIdeal`, so
`a / s` and `a · t` have the same residue for any `t` inverting `s` there.  That surjectivity
(`residueHomSome_surjective`) is the whole content; everything else is formal:

* the first isomorphism theorem gives `κ(some v) ≃ₐ[F] F[W] ⧸ v.asIdeal`;
* `F[W]` is a finite-type `F`-algebra (it is module-finite over `F[X]`), so `κ(some v)` is too, and
  Zariski's lemma (`finite_of_finite_type_of_isJacobsonRing`) makes it a **finite** extension of
  `F` — this needs nothing about `F`;
* a finite extension of an algebraically closed field is trivial
  (`IsAlgClosed.algebraMap_bijective_of_isIntegral`), which is `residueDegreeProj_some_eq_one`.

## The point at infinity is *not* here (`#749`)

`residueDegreeProj W none = 1` is **not** proved below, and the reason is structural rather than a
matter of effort: `placeOf W none = ordInftyValuationSubring W` is cut out by `0 ≤ ordInfty` and is
**not presented as a localisation of a finitely-generated `F`-algebra**, so no step of the route
above transfers — there is nothing for `IsLocalization.AtPrime.to_map_mem_maximal_iff` or Zariski's
lemma to bite on.

The statement there should be **unconditional** in `F`, unlike the affine one: the point at infinity
is rational over any base field.  The route is a leading-coefficient argument on the basis `{1, y}`
of `F[W]` over `F[X]`, whose key point is a parity observation.  For `a = p • 1 + q • y`,
`CoordinateRing.degree_norm_smul_basis` gives

```
deg W a  =  max (2 • p.degree) (2 • q.degree + 3)
```

and the two entries are *even-or-`⊥`* and *odd-or-`⊥`*, so they are never equal: the parity of
`deg W a` says which one attains the maximum, and the leading coefficient of `a` is therefore a
single element of `F`.  That is what makes the residue field `F` and not a quadratic extension of
it — a norm-based argument would only pin the constant down up to a square root.  `#749` carries
the full route.

Consequently the *uniform* statement `∀ p, residueDegreeProj W p = 1` is also not available yet;
`residueDegreeProj_some_eq_one` is stated at `some v` and must be used there.

## What is *not* here

* `residueDegreeProj W none`, in any form, and the uniform corollary over all of
  `ProjPoint W` (`#749`).
* Any comparison with `degPt` (`DivisorDegree.lean`), which is
  `Ideal.natDegreeGenerator (Ideal.relNorm F[X] v.asIdeal)` — a *relative ideal norm to `F[X]`*,
  not a residue-field degree.  The two agree; nothing below assumes it.
* The relative residue degree `[κ(p) : κ(q)]` along `[2]`, the contraction `κ(q) → κ(p)`,
  ramification indices, and the fundamental identity `∑ e_p · f_p = 4`.
* `IsDiscreteValuationRing (placeOf W p)`; `[3]∗`; Ward; `#418`; `#465`.

Ward-independent and `#418`-independent throughout: `[Field F]` and
`[IsDedekindDomain W.CoordinateRing]`, with `[IsAlgClosed F]` added only where it is genuinely
used, and no `[W.IsElliptic]`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.1–II.2.
* Stichtenoth, *Algebraic Function Fields and Codes*, I.1 (the residue field of a place).
-/

open IsDedekindDomain

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]
  (v : HeightOneSpectrum W.CoordinateRing)

/-! ### An affine place is a localisation of the coordinate ring

`placeOf W (some v)` is *definitionally* `valuationSubringAtPrime W.FunctionField v`
(`placeOf_some` is `rfl`), so Mathlib's `F[W]`-algebra and localisation instances transfer by
`inferInstanceAs`.  They are restated here because instance search does not unfold `placeOf`. -/

/-- The coordinate ring maps into every affine place. -/
noncomputable instance instAlgebraCoordinateRingPlaceOfSome :
    Algebra W.CoordinateRing (placeOf W (some v)) :=
  inferInstanceAs (Algebra W.CoordinateRing
    (HeightOneSpectrum.valuationSubringAtPrime W.FunctionField v))

instance : IsScalarTower W.CoordinateRing (placeOf W (some v)) W.FunctionField :=
  inferInstanceAs (IsScalarTower W.CoordinateRing
    (HeightOneSpectrum.valuationSubringAtPrime W.FunctionField v) W.FunctionField)

/-- **An affine place is the localisation of `F[W]` at that point.** -/
instance : IsLocalization v.asIdeal.primeCompl (placeOf W (some v)) :=
  inferInstanceAs (IsLocalization v.asIdeal.primeCompl
    (HeightOneSpectrum.valuationSubringAtPrime W.FunctionField v))

/-- The constant field acts through the coordinate ring: the `F`-algebra structure of
`instAlgebraPlaceOf` factors through `F[W]`. -/
instance : IsScalarTower F W.CoordinateRing (placeOf W (some v)) :=
  IsScalarTower.of_algebraMap_eq fun c => Subtype.ext (by
    rw [coe_algebraMap_placeOf]
    change algebraMap F W.FunctionField c
      = algebraMap W.CoordinateRing W.FunctionField (algebraMap F W.CoordinateRing c)
    exact IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField c)

instance : IsScalarTower F W.CoordinateRing (residueFieldProj W (some v)) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change IsLocalRing.residue _ (algebraMap F (placeOf W (some v)) c) = _
    rw [IsScalarTower.algebraMap_apply F W.CoordinateRing (placeOf W (some v))]
    rfl

/-! ### The residue map out of the coordinate ring -/

/-- **The residue map of an affine place, read on the coordinate ring**: reduce into the place,
then take the residue.  Its kernel is `v.asIdeal` (`ker_residueHomSome`) and it is surjective
(`residueHomSome_surjective`), so it identifies `κ(some v)` with `F[W] ⧸ v.asIdeal`. -/
noncomputable def residueHomSome : W.CoordinateRing →ₐ[F] residueFieldProj W (some v) :=
  (Algebra.ofId W.CoordinateRing (residueFieldProj W (some v))).restrictScalars F

lemma residueHomSome_apply (a : W.CoordinateRing) :
    residueHomSome v a
      = IsLocalRing.residue _ (algebraMap W.CoordinateRing (placeOf W (some v)) a) :=
  rfl

/-- **A function on the affine chart vanishes at `v` exactly when it lies in `v`.**  This is
`IsLocalization.AtPrime.to_map_mem_maximal_iff`, read through the residue map; unlike
`mem_maximalIdeal_placeOf_iff` it needs no nonvanishing hypothesis, because `v.asIdeal` is an
honest ideal rather than a locus of the junk-valued order function. -/
lemma ker_residueHomSome :
    RingHom.ker ((residueHomSome v).toRingHom : W.CoordinateRing →+* _) = v.asIdeal := by
  ext a
  rw [RingHom.mem_ker]
  change IsLocalRing.residue _ (algebraMap W.CoordinateRing (placeOf W (some v)) a) = 0 ↔ _
  rw [IsLocalRing.residue_eq_zero_iff]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff _ v.asIdeal a

/-- **Every residue at an affine place is the residue of a function regular on the affine chart.**

An element of the place is `a / s` with `s ∉ v.asIdeal`; since `v.asIdeal` is maximal, `s` has an
inverse `t` modulo it, and then `a / s` and `a · t` have the same residue.  This is the one step
that uses that the place *is* the localisation, and everything else in this file is formal. -/
theorem residueHomSome_surjective : Function.Surjective (residueHomSome (W := W) v) := by
  intro ξ
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective ξ
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl y
  obtain ⟨t, ht⟩ : ∃ t : W.CoordinateRing, residueHomSome v s * residueHomSome v t = 1 := by
    letI : Field (W.CoordinateRing ⧸ v.asIdeal) := Ideal.Quotient.field _
    have hs : (Ideal.Quotient.mk v.asIdeal (s : W.CoordinateRing)) ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
      exact s.2
    obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.1 (isUnit_iff_ne_zero.2 hs)
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective u
    refine ⟨t, ?_⟩
    rw [← map_mul]
    have hmem : (s : W.CoordinateRing) * t - 1 ∈ v.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hu, map_one, sub_self]
    have hz : residueHomSome v ((s : W.CoordinateRing) * t - 1) = 0 :=
      (ker_residueHomSome (W := W) v).ge hmem
    rw [map_sub, map_one, sub_eq_zero] at hz
    exact hz
  refine ⟨a * t, ?_⟩
  have h1 := congrArg (IsLocalRing.residue (placeOf W (some v)))
    (IsLocalization.mk'_spec (placeOf W (some v)) a s)
  rw [map_mul] at h1
  have key : IsLocalRing.residue (placeOf W (some v)) (IsLocalization.mk' _ a s)
      * residueHomSome v (s : W.CoordinateRing) = residueHomSome v a := h1
  rw [map_mul, ← key, mul_assoc, ht, mul_one]

/-! ### The residue field of an affine place -/

/-- **The residue field of an affine closed point is the quotient of the coordinate ring by that
point**, as `F`-algebras: the first isomorphism theorem applied to `residueHomSome`. -/
noncomputable def residueFieldProjSomeEquiv :
    residueFieldProj W (some v) ≃ₐ[F] (W.CoordinateRing ⧸ v.asIdeal) :=
  ((Ideal.quotientEquivAlgOfEq F (ker_residueHomSome (W := W) v)).symm.trans
    (Ideal.quotientKerAlgEquivOfSurjective (residueHomSome_surjective (W := W) v))).symm

@[simp]
lemma residueFieldProjSomeEquiv_symm_mk (a : W.CoordinateRing) :
    (residueFieldProjSomeEquiv (W := W) v).symm (Ideal.Quotient.mk v.asIdeal a)
      = residueHomSome v a :=
  rfl

instance : Algebra.FiniteType F (residueFieldProj W (some v)) :=
  Algebra.FiniteType.of_surjective (residueHomSome v) (residueHomSome_surjective v)

/-- **Zariski's lemma at an affine place.**  `F[W]` is a finite-type `F`-algebra, hence so is its
residue field at `v`; a field of finite type over a field is finite over it.  No hypothesis on `F`
is needed — in particular this is where `residueDegreeProj W (some v) ≠ 0` comes from. -/
instance : Module.Finite F (residueFieldProj W (some v)) :=
  finite_of_finite_type_of_isJacobsonRing F (residueFieldProj W (some v))

/-- **The residue degree at an affine place is nonzero.**  `residueDegreeProj` is a `Module.finrank`
and so returns the junk value `0` on an infinite-dimensional extension; this rules that out. -/
theorem residueDegreeProj_some_ne_zero : residueDegreeProj W (some v) ≠ 0 :=
  Module.finrank_pos.ne'

/-- **Over an algebraically closed base field every affine closed point is rational**, i.e. its
residue field is `F` itself.  A finite extension of an algebraically closed field is trivial. -/
theorem algebraMap_residueFieldProj_some_bijective [IsAlgClosed F] :
    Function.Bijective (algebraMap F (residueFieldProj W (some v))) :=
  IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- **The residue degree of an affine closed point over an algebraically closed field is `1`.** -/
theorem residueDegreeProj_some_eq_one [IsAlgClosed F] : residueDegreeProj W (some v) = 1 :=
  (residueDegreeProj_eq_one_iff_surjective (some v)).2
    (algebraMap_residueFieldProj_some_bijective v).2

/-! ### Non-vacuity

Everything above carries `[IsDedekindDomain W.CoordinateRing]`, and the headline additionally
carries `[IsAlgClosed F]`, so a curve on which the whole chain elaborates with every instance
discharged is committed rather than quoted.  Two curves appear, for two different reasons.

`y² = x³ - x` over `ℚ` (discriminant `64`) is the certificate curve `PullbackDivisor.lean`,
`MulByTwoPlaceAtInfinity.lean` and `PlaceResidueField.lean` use; it carries the Dedekind instance
but **not** `IsAlgClosed`, so it certifies the hypothesis-free statements and, in particular, the
`#742` maximal-ideal characterisation fired on a *named* function.

The same equation over `AlgebraicClosure ℚ` — the base field `WeilPairingAlternatingTwo.lean` and
`WeilPairingAntisymmetricMu.lean` use — certifies the headline. -/

section Nonvacuity

/-- The curve `y² = x³ - x` over `ℚ`, of discriminant `64`. -/
private def exampleCurve : Affine ℚ := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

open CoordinateRing in
/-- **`#742` deliverable 5, on a named function.**  `x` has a double pole at infinity, so `x⁻¹`
has order `+2` there and therefore lies in the maximal ideal of the place at infinity — the
maximal-ideal characterisation of `PlaceResidueField.lean` fired on a function one can name, rather
than on a uniformizer produced by an existential. -/
example : (⟨(genX exampleCurve)⁻¹, (mem_placeOf_iff_divisorProj_nonneg (W := exampleCurve) none
      (inv_ne_zero genX_ne_zero)).2 (by
        rw [divisorProj_inv, Finsupp.neg_apply, divisorProj_genX_apply_none]; norm_num)⟩ :
    placeOf exampleCurve none) ∈ IsLocalRing.maximalIdeal (placeOf exampleCurve none) := by
  rw [mem_maximalIdeal_placeOf_iff
    (by simpa using inv_ne_zero (genX_ne_zero (W := exampleCurve)))]
  rw [divisorProj_inv, Finsupp.neg_apply, divisorProj_genX_apply_none]
  norm_num

open CoordinateRing in
/-- The kernel form of the same certificate: `x⁻¹` has residue `0` at infinity. -/
example : IsLocalRing.residue (placeOf exampleCurve none)
    ⟨(genX exampleCurve)⁻¹, (mem_placeOf_iff_divisorProj_nonneg (W := exampleCurve) none
      (inv_ne_zero genX_ne_zero)).2 (by
        rw [divisorProj_inv, Finsupp.neg_apply, divisorProj_genX_apply_none]; norm_num)⟩ = 0 := by
  rw [residue_placeOf_eq_zero_iff
    (by simpa using inv_ne_zero (genX_ne_zero (W := exampleCurve)))]
  rw [divisorProj_inv, Finsupp.neg_apply, divisorProj_genX_apply_none]
  norm_num

/-- The residue field at every affine closed point of a curve over `ℚ` is a *finite* extension of
`ℚ` — Zariski's lemma, with no hypothesis on the base field. -/
example (v : HeightOneSpectrum exampleCurve.CoordinateRing) :
    Module.Finite ℚ (residueFieldProj exampleCurve (some v)) :=
  inferInstance

example (v : HeightOneSpectrum exampleCurve.CoordinateRing) :
    residueDegreeProj exampleCurve (some v) ≠ 0 :=
  residueDegreeProj_some_ne_zero v

/-- An algebraically closed field of characteristic zero. -/
private abbrev exampleFieldBar : Type := AlgebraicClosure ℚ

/-- The same curve `y² = x³ - x`, now over `AlgebraicClosure ℚ`. -/
private noncomputable def exampleCurveBar : Affine exampleFieldBar := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurveBar.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurveBar, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- **The headline, committed.**  Every affine closed point of a genuine curve over a genuine
algebraically closed field has residue degree `1`. -/
example (v : HeightOneSpectrum exampleCurveBar.CoordinateRing) :
    residueDegreeProj exampleCurveBar (some v) = 1 :=
  residueDegreeProj_some_eq_one v

/-- There is at least one affine closed point to say that about. -/
example : Nonempty (HeightOneSpectrum exampleCurveBar.CoordinateRing) :=
  nonempty_heightOneSpectrum

end Nonvacuity

end WeierstrassCurve.Affine
