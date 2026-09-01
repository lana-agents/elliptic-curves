/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.PlaceBelowIntegralClosure
import EllipticCurves.FunctionField.PullbackDivisor

/-!
# The `primesOver` ↔ fibre dictionary

`EllipticCurves.FunctionField.PlaceBelowIntegralClosure` (`#754`) names the valuation ring
`placeBelow φ q` of the place of the subfield `L = φ F(W)` below `q`, and supplies both module
hypotheses of

```lean
-- Mathlib/RingTheory/RamificationInertia/Basic.lean
theorem Ideal.sum_ramification_inertia_eq_finrank
    [IsDomain R] [Module.Finite R S] [Module.Flat R S] [Fintype (p.primesOver S)] :
    ∑ q : p.primesOver S, q.1.ramificationIdx R * q.1.inertiaDeg R = Module.finrank R S
```

together with its right-hand side.  What is missing is the **index set**: that theorem sums over the
primes of `B = integralClosure (placeBelow φ q) F(W)` lying over the maximal ideal of
`placeBelow φ q`, whereas this development indexes places by `ProjPoint W` and the fibre of the
contraction `comapProjPoint φ`.  This file identifies the two.

## The dictionary

```lean
primesOverEquivFibre :
  ↥((IsLocalRing.maximalIdeal ↥(placeBelow φ q)).primesOver ↥(integralClosure _ F(W)))
    ≃ ↥(comapProjPoint hφF hφint ⁻¹' {q})
```

Both directions are the classical correspondence "a prime of the integral closure is the centre of
a place above".  Nothing here is definitional, and the two halves use different engines:

* **from a prime to a point.**  `B` is a Dedekind domain with fraction field `F(W)` — that is
  `integralClosure.isDedekindDomain` and `integralClosure.isFractionRing_of_finite_extension`, which
  need exactly the finiteness and separability `#754` already isolated — so a nonzero prime `P` of
  `B` has a localisation `B_P`, a valuation subring of `F(W)`, and
  `EllipticCurves.FunctionField.Places` names it `placeOf W p` for a unique `p`;
* **from a point to a prime.**  For `p` in the fibre, `B ⊆ placeOf W p`, because a valuation subring
  is integrally closed in the ambient field; so
  `EllipticCurves.FunctionField.ValuationSubringDedekind`'s `exists_valuationSubringAtPrime_eq` —
  every proper valuation subring of `F(W)` containing `B` is a localisation of `B` — produces the
  prime.

The condition cutting out the fibre is `under_asIdeal_eq_maximalIdeal_iff`, which is the heart of
the file: for a height-one prime `v` of `B`,

```
(B_v ∩ L = placeBelow φ q)   ↔   (v.asIdeal lies over the maximal ideal of placeBelow φ q).
```

Its proof is elementary — no ramification theory, only `ValuationSubring.mem_nonunits_iff_or`
(`x` is a nonunit iff `x = 0` or `x⁻¹ ∉ A`) applied once in `L` and once in `F(W)`.  The left-hand
side is what `#754`'s `placeBelow_comapProjPoint` translates into membership of the fibre.

## Main results

* `WeierstrassCurve.Affine.placeBelow_injective` and
  `WeierstrassCurve.Affine.comapProjPoint_eq_iff_placeBelow_eq` — the fibre condition, moved from
  `ProjPoint W` down to the valuation rings of `L`;
* `WeierstrassCurve.Affine.mem_placeOf_of_mem_integralClosure` — `B ⊆ placeOf W p` for `p` in the
  fibre;
* `WeierstrassCurve.Affine.projPointOfHeightOne` — the point of the projective curve carrying the
  localisation of `B` at a height-one prime, with
  `WeierstrassCurve.Affine.placeOf_projPointOfHeightOne` computing its place;
* **`WeierstrassCurve.Affine.under_asIdeal_eq_maximalIdeal_iff`** — the fibre condition, as a
  statement about ideals;
* **`WeierstrassCurve.Affine.primesOverEquivFibre`** — the dictionary;
* `WeierstrassCurve.Affine.nonempty_fibre_comapProjPoint` — the fibre is **nonempty**, which is
  the first consequence the Weil-pairing front wants and which does not need the identity;
* `WeierstrassCurve.Affine.CoordinateRing.primesOverEquivFibreTwo` and its companions — the `[2]∗`
  instantiation.

## What is *not* here

**The fundamental identity `∑_{p ↦ q} e_p · f_p = 4` is not proved here.**  Firing
`Ideal.sum_ramification_inertia_eq_finrank` through this dictionary needs two further
compatibilities, and both are theorems rather than transports of a definition:

* `Ideal.ramificationIdx (algebraMap A B) 𝔪 P = (ramificationIdxTwo h2 p).toNat` — Mathlib's index
  is a `sSup` over powers, while `ramificationIdxTwo` is extracted by choice from
  `exists_ramificationIdx` and characterised only through `divisorProj_comp_apply`;
* `Ideal.inertiaDeg 𝔪 P = residueDegreeTwo h2 p` — which needs the residue field of `B` at `P` to be
  identified with the residue field of `placeOf W p`.

`#755` prices the dictionary separately from the identity for exactly this reason, and this file is
the dictionary.  Both compatibilities and the identity itself are
`EllipticCurves.FunctionField.PlaceRamificationInertia` (`#763`), which imports this file: the first
is proved there in general, the second there only in the form `Ideal.inertiaDeg 𝔪 P = 1` over
`[IsAlgClosed F]`.

⚠️ **The clause this paragraph used to end with has been paid.**  It read *"the general
`= residueDegreeTwo h2 p` is still open, and is the one statement this paragraph names that
remains unproved"*.  `ideal_inertiaDeg_eq_residueDegreeComap`
(`EllipticCurves.FunctionField.PlaceInertiaGeneral`, `#1167`) proves
`Ideal.inertiaDeg 𝔪 P = residueDegreeComap hφF hφint p` for an **arbitrary** `φ` and, in its own
words, *"assumes nothing about `F`"*; `residueDegreeTwo` is `residueDegreeComap` at `mulByTwoEndo`
by definition, so `φ = [2]∗` is exactly the statement named above.  ⚠️ Everything else in the
paragraph stands: the ramification clause was already general, and `#763` really does prove only
the `[IsAlgClosed F]` form of the inertia one — the general form is downstream of it, in
`PlaceInertiaGeneral`, which imports `PlaceRamificationInertia`, which imports this file.

Also not here: `[3]∗` and general `[n]∗` (the degree `4` is `[2]`-specific, but everything before
the `[2]∗` section of this file is stated for an arbitrary `φ` and serves them unchanged — the
`[3]∗` instantiation is `EllipticCurves.FunctionField.MulByThreeRamification`, and general `[n]∗`
has no case here); `#E[n] = n²`; and any comparison with `degPt`.

⚠️ **The reason clause the general-`[n]∗` parenthetical used to give has been paid** — it read
*"`mulByNEndo` not existing"*.  `[n]∗` at every `n` is `mulByNEndo`,
`EllipticCurves.FunctionField.MulByNPullback`, with its place layer in
`EllipticCurves.FunctionField.MulByNPlacePullback`.  What keeps the identity above `[2]`-specific
is its right-hand side `4`, not the endomorphism.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
* Stichtenoth, *Algebraic Function Fields and Codes*, III.1.
-/

open IsDedekindDomain Module

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]
  {φ : W.FunctionField →+* W.FunctionField} {q : ProjPoint W}

/-! ### The fibre condition, moved down to the subfield

`placeBelow φ` is injective, so a point of the projective curve lies in the fibre of
`comapProjPoint φ` over `q` exactly when its place meets `L` in `placeBelow φ q`.  This is the form
the dictionary needs, because a prime of the integral closure knows about `L` and knows nothing
about `ProjPoint W`. -/

/-- **`placeBelow φ` is injective.**  It is `placeOf` composed with the `comap` along a ring
*isomorphism*, and `placeOf` is injective by the classification of places (`#651`). -/
theorem placeBelow_injective : Function.Injective (placeBelow (W := W) φ) := by
  intro q q' h
  refine placeOf_injective (SetLike.ext fun z => ?_)
  have := SetLike.ext_iff.1 h (φ.rangeRestrictFieldEquiv z)
  rw [mem_placeBelow_iff, mem_placeBelow_iff, RingEquiv.symm_apply_apply] at this
  exact this

variable (hφF : ∀ c : F, φ (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c)
  (hφint : ∀ z : W.FunctionField, φ.IsIntegralElem z)

include hφF hφint in
/-- **`p` lies in the fibre over `q` iff `L ∩ placeOf W p` is the place below `q`.**  Immediate from
`#754`'s `placeBelow_comapProjPoint` and injectivity, and it is what turns the dictionary's ideal
condition into membership of the fibre. -/
theorem comapProjPoint_eq_iff_placeBelow_eq {p : ProjPoint W} :
    comapProjPoint hφF hφint p = q
      ↔ (placeOf W p).comap (φ.fieldRange.subtype : ↥φ.fieldRange →+* W.FunctionField)
          = placeBelow φ q := by
  rw [← placeBelow_comapProjPoint hφF hφint p]
  exact ⟨fun h => by rw [h], fun h => placeBelow_injective h⟩

include hφF in
/-- The place below `q` sits inside `placeOf W p` for every `p` in the fibre over `q`. -/
theorem algebraMap_placeBelow_mem_placeOf {p : ProjPoint W}
    (hp : comapProjPoint hφF hφint p = q) (a : ↥(placeBelow φ q)) :
    algebraMap ↥(placeBelow φ q) W.FunctionField a ∈ placeOf W p := by
  have h : placeBelow φ q
      = (placeOf W p).comap (φ.fieldRange.subtype : ↥φ.fieldRange →+* W.FunctionField) :=
    ((comapProjPoint_eq_iff_placeBelow_eq hφF hφint).1 hp).symm
  exact (SetLike.ext_iff.1 h (a : ↥φ.fieldRange)).1 a.2

include hφF in
/-- **The integral closure sits inside every place of the fibre.**  A valuation subring is
integrally closed in the ambient field (`ValuationSubring.mem_of_isIntegralElem`, `#668`), and every
element of `B` is integral over the place below. -/
theorem mem_placeOf_of_mem_integralClosure {p : ProjPoint W}
    (hp : comapProjPoint hφF hφint p = q) {b : W.FunctionField}
    (hb : b ∈ integralClosure ↥(placeBelow φ q) W.FunctionField) :
    b ∈ placeOf W p :=
  ValuationSubring.mem_of_isIntegralElem _ _ (algebraMap_placeBelow_mem_placeOf hφF hφint hp) hb

/-! ### The base field lands in the integral closure

`exists_placeOf_eq` asks for a valuation subring containing `F`, so the point attached to a prime of
`B` needs `F ⊆ B`.  It holds for the cheapest possible reason: `φ` fixes `F`, so `F ⊆ L`, and `F` is
contained in every place, so `F ⊆ placeBelow φ q ⊆ B`. -/

include hφF in
/-- An element of `L` that is a scalar is in the place below, whichever `q` it is taken at. -/
theorem mem_placeBelow_of_coe_eq_algebraMap (c : F) (y : ↥φ.fieldRange)
    (hy : (y : W.FunctionField) = algebraMap F W.FunctionField c) : y ∈ placeBelow φ q := by
  rw [mem_placeBelow_iff]
  have hz : φ.rangeRestrictFieldEquiv.symm y = algebraMap F W.FunctionField c :=
    φ.injective (by rw [RingHom.rangeRestrictFieldEquiv_apply_symm_apply, hφF, hy])
  rw [hz]
  exact algebraMap_mem_placeOf q c

include hφF in
/-- **The base field lies in the integral closure**, because it already lies in the place below. -/
theorem algebraMap_base_mem_integralClosure_placeBelow (c : F) :
    algebraMap F W.FunctionField c ∈ integralClosure ↥(placeBelow φ q) W.FunctionField :=
  isIntegral_algebraMap (x := (⟨_, mem_placeBelow_of_coe_eq_algebraMap hφF c
    ⟨algebraMap F W.FunctionField c, ⟨algebraMap F W.FunctionField c, hφF c⟩⟩ rfl⟩ :
    ↥(placeBelow φ q)))

/-! ### The integral closure is a Dedekind domain with fraction field `F(W)`

These are the two instances the localisation theory needs, and they are exactly `#754`'s hypotheses
again: `Module.Finite` and `Algebra.IsSeparable` of `F(W)` over `L`.  They are declared as instances
rather than theorems because `HeightOneSpectrum.valuationSubringAtPrime` cannot even be *stated*
without them, so a `haveI` at the use site is not available. -/

section Dedekind

variable [Module.Finite ↥φ.fieldRange W.FunctionField]
  [Algebra.IsSeparable ↥φ.fieldRange W.FunctionField]

/-- **`F(W)` is the fraction field of `B`.** -/
instance instIsFractionRingIntegralClosurePlaceBelow (q : ProjPoint W) :
    IsFractionRing ↥(integralClosure ↥(placeBelow φ q) W.FunctionField) W.FunctionField :=
  integralClosure.isFractionRing_of_finite_extension ↥φ.fieldRange W.FunctionField

/-- **`B` is a Dedekind domain**, the integral closure of a discrete valuation ring (`#753`, `#754`)
in a finite separable extension of its fraction field. -/
instance instIsDedekindDomainIntegralClosurePlaceBelow (q : ProjPoint W) :
    IsDedekindDomain ↥(integralClosure ↥(placeBelow φ q) W.FunctionField) :=
  integralClosure.isDedekindDomain ↥(placeBelow φ q) ↥φ.fieldRange W.FunctionField

/-- `B` is torsion-free over the place below; this is what forces a prime lying over the maximal
ideal to be nonzero, hence height one. -/
instance instIsTorsionFreeIntegralClosurePlaceBelow (q : ProjPoint W) :
    Module.IsTorsionFree ↥(placeBelow φ q)
      ↥(integralClosure ↥(placeBelow φ q) W.FunctionField) :=
  IsIntegralClosure.isTorsionFree ↥(placeBelow φ q) W.FunctionField

omit [Module.Finite ↥φ.fieldRange W.FunctionField]
  [Algebra.IsSeparable ↥φ.fieldRange W.FunctionField] in
/-- The place below is a discrete valuation ring, hence not a field, so its maximal ideal is
nonzero. -/
theorem maximalIdeal_placeBelow_ne_bot (q : ProjPoint W) :
    IsLocalRing.maximalIdeal ↥(placeBelow φ q) ≠ ⊥ :=
  IsDiscreteValuationRing.not_a_field _

include hφF in
/-- The base field lies in every localisation of `B`. -/
theorem algebraMap_base_mem_valuationSubringAtPrime
    (v : HeightOneSpectrum ↥(integralClosure ↥(placeBelow φ q) W.FunctionField)) (c : F) :
    algebraMap F W.FunctionField c
      ∈ HeightOneSpectrum.valuationSubringAtPrime W.FunctionField v :=
  HeightOneSpectrum.algebraMap_mem_valuationSubringAtPrime (K := W.FunctionField) v
    ⟨algebraMap F W.FunctionField c, algebraMap_base_mem_integralClosure_placeBelow hφF c⟩

variable (φ) in
/-- **The point of the projective curve carrying the localisation of `B` at `v`.**

`B_v` is a proper valuation subring of `F(W)` containing `F`, so the classification of places
(`#651`) names it.  This is the "prime to point" half of the dictionary; it is defined by
`placeEquiv.symm` rather than by choice so that `placeOf_projPointOfHeightOne` is a projection. -/
noncomputable def projPointOfHeightOne (q : ProjPoint W)
    (v : HeightOneSpectrum ↥(integralClosure ↥(placeBelow φ q) W.FunctionField)) : ProjPoint W :=
  (placeEquiv W).symm ⟨HeightOneSpectrum.valuationSubringAtPrime W.FunctionField v,
    algebraMap_base_mem_valuationSubringAtPrime hφF v,
    HeightOneSpectrum.valuationSubringAtPrime_ne_top v⟩

@[simp]
theorem placeOf_projPointOfHeightOne
    (v : HeightOneSpectrum ↥(integralClosure ↥(placeBelow φ q) W.FunctionField)) :
    placeOf W (projPointOfHeightOne φ hφF q v)
      = HeightOneSpectrum.valuationSubringAtPrime W.FunctionField v :=
  placeOf_placeEquiv_symm _

/-- **`projPointOfHeightOne` is injective**: distinct primes localise to distinct valuation
subrings (`valuationSubringAtPrime_injective`), and distinct places are distinct points. -/
theorem projPointOfHeightOne_injective :
    Function.Injective (projPointOfHeightOne φ hφF q) := fun v w h =>
  HeightOneSpectrum.valuationSubringAtPrime_injective (K := W.FunctionField)
    (by rw [← placeOf_projPointOfHeightOne hφF v, ← placeOf_projPointOfHeightOne hφF w, h])

/-! ### The fibre condition, as a statement about ideals

This is the heart of the file.  For a height-one prime `v` of `B`, the intersection `B_v ∩ L` is the
place below `q` exactly when `v.asIdeal` lies over the maximal ideal of that place.  Both directions
run on `ValuationSubring.mem_nonunits_iff_or` — `x` is a nonunit of a valuation subring iff `x = 0`
or `x⁻¹` is outside it — applied once in `L` and once in `F(W)`; no ramification theory enters. -/

variable (v : HeightOneSpectrum ↥(integralClosure ↥(placeBelow φ q) W.FunctionField))

omit hφF in
/-- `placeBelow φ q ⊆ B ⊆ B_v`, read inside `L`. -/
theorem placeBelow_le_comap_valuationSubringAtPrime :
    placeBelow φ q ≤ (HeightOneSpectrum.valuationSubringAtPrime W.FunctionField v).comap
      (φ.fieldRange.subtype : ↥φ.fieldRange →+* W.FunctionField) := by
  intro y hy
  rw [ValuationSubring.mem_comap]
  have h := HeightOneSpectrum.algebraMap_mem_valuationSubringAtPrime (K := W.FunctionField) v
    (algebraMap ↥(placeBelow φ q) ↥(integralClosure ↥(placeBelow φ q) W.FunctionField) ⟨y, hy⟩)
  rwa [← IsScalarTower.algebraMap_apply] at h

omit hφF in
/-- Membership in `v.asIdeal`, for an element of the place below, is being a nonunit of `B_v`.
This is `mem_asIdeal_iff_mem_nonunits` (`#651`'s `ValuationSubringDedekind`) read along the tower
`placeBelow φ q → B → F(W)`. -/
theorem algebraMap_mem_asIdeal_iff (a : ↥(placeBelow φ q)) :
    algebraMap ↥(placeBelow φ q) ↥(integralClosure ↥(placeBelow φ q) W.FunctionField) a
        ∈ v.asIdeal
      ↔ ((a : ↥φ.fieldRange) : W.FunctionField)
          ∈ (HeightOneSpectrum.valuationSubringAtPrime W.FunctionField v).nonunits := by
  rw [HeightOneSpectrum.mem_asIdeal_iff_mem_nonunits (K := W.FunctionField),
    ← IsScalarTower.algebraMap_apply]
  rfl

omit hφF in
/-- **The dictionary's defining condition.**  `v` lies over the maximal ideal of the place below `q`
exactly when the localisation of `B` at `v` meets `L` in that place.

The forward direction is a two-line unfolding through the nonunits.  The backward direction is the
one with content: if `y ∈ L` lies in `B_v` but not in the place below, then `y⁻¹` is a nonunit
there, hence in `v.asIdeal`, hence a nonunit of `B_v` — but `y ∈ B_v` makes it a unit. -/
theorem under_asIdeal_eq_maximalIdeal_iff :
    Ideal.under ↥(placeBelow φ q) v.asIdeal = IsLocalRing.maximalIdeal ↥(placeBelow φ q)
      ↔ (HeightOneSpectrum.valuationSubringAtPrime W.FunctionField v).comap
          (φ.fieldRange.subtype : ↥φ.fieldRange →+* W.FunctionField) = placeBelow φ q := by
  constructor
  · intro hlies
    refine le_antisymm (fun y hy => ?_) (placeBelow_le_comap_valuationSubringAtPrime v)
    rw [ValuationSubring.mem_comap] at hy
    by_contra hyA
    have hy0 : y ≠ 0 := fun h => hyA (h ▸ zero_mem _)
    obtain hinv | hinv := (placeBelow φ q).mem_or_inv_mem y
    · exact hyA hinv
    · have hmax : (⟨y⁻¹, hinv⟩ : ↥(placeBelow φ q)) ∈ IsLocalRing.maximalIdeal _ := by
        rw [← ValuationSubring.coe_mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]
        exact Or.inr (by rwa [inv_inv])
      rw [← hlies, Ideal.mem_under, algebraMap_mem_asIdeal_iff,
        ValuationSubring.mem_nonunits_iff_or] at hmax
      rcases hmax with h | h
      · exact hy0 (by simpa using h)
      · exact h (by rwa [Subfield.coe_inv, inv_inv])
  · intro hcomp
    have hmem : ∀ z : ↥φ.fieldRange, z ∈ placeBelow φ q
        ↔ (z : W.FunctionField)
          ∈ HeightOneSpectrum.valuationSubringAtPrime W.FunctionField v :=
      fun z => (SetLike.ext_iff.1 hcomp z).symm
    refine Ideal.ext fun a => ?_
    rw [Ideal.mem_under, algebraMap_mem_asIdeal_iff, ← ValuationSubring.coe_mem_nonunits_iff,
      ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or]
    have hz : ((a : ↥φ.fieldRange) : W.FunctionField) = 0 ↔ (a : ↥φ.fieldRange) = 0 := by
      exact_mod_cast Iff.rfl
    have hi : ((a : ↥φ.fieldRange) : W.FunctionField)⁻¹
        ∈ HeightOneSpectrum.valuationSubringAtPrime W.FunctionField v
        ↔ (a : ↥φ.fieldRange)⁻¹ ∈ placeBelow φ q := by
      rw [hmem, Subfield.coe_inv]
    rw [hz, hi]

include hφint in
/-- **The point attached to `v` lies in the fibre over `q` iff `v` lies over the maximal ideal.**
The two previous results, composed. -/
theorem comapProjPoint_projPointOfHeightOne_eq_iff :
    comapProjPoint hφF hφint (projPointOfHeightOne φ hφF q v) = q
      ↔ Ideal.under ↥(placeBelow φ q) v.asIdeal = IsLocalRing.maximalIdeal ↥(placeBelow φ q) := by
  rw [comapProjPoint_eq_iff_placeBelow_eq hφF hφint, placeOf_projPointOfHeightOne hφF v,
    under_asIdeal_eq_maximalIdeal_iff]

include hφint in
/-- **Every point of the fibre comes from a prime.**  `B` is contained in `placeOf W p`, which is a
proper valuation subring of `F(W)`, so `exists_valuationSubringAtPrime_eq` produces the prime. -/
theorem exists_projPointOfHeightOne_eq {p : ProjPoint W} (hp : comapProjPoint hφF hφint p = q) :
    ∃ v, projPointOfHeightOne φ hφF q v = p := by
  obtain ⟨v, hv⟩ := IsDedekindDomain.exists_valuationSubringAtPrime_eq (placeOf W p)
    (fun b : ↥(integralClosure ↥(placeBelow φ q) W.FunctionField) =>
      mem_placeOf_of_mem_integralClosure hφF hφint hp b.2) (placeOf_ne_top p)
  exact ⟨v, placeOf_injective (by rw [placeOf_projPointOfHeightOne hφF v, hv])⟩

/-! ### The dictionary -/

omit hφF in
/-- The height-one prime underlying a member of `primesOver`.  A prime lying over the maximal ideal
of the place below is nonzero, hence height one: `B` is torsion-free over a domain whose maximal
ideal is nonzero. -/
def heightOneOfPrimesOver
    (P : ↥((IsLocalRing.maximalIdeal ↥(placeBelow φ q)).primesOver
      ↥(integralClosure ↥(placeBelow φ q) W.FunctionField))) :
    HeightOneSpectrum ↥(integralClosure ↥(placeBelow φ q) W.FunctionField) :=
  ⟨P.1, P.2.1, Ideal.ne_bot_of_mem_primesOver (maximalIdeal_placeBelow_ne_bot q) P.2⟩

omit [Module.Finite ↥φ.fieldRange W.FunctionField]
  [Algebra.IsSeparable ↥φ.fieldRange W.FunctionField] in
@[simp]
theorem asIdeal_heightOneOfPrimesOver
    (P : ↥((IsLocalRing.maximalIdeal ↥(placeBelow φ q)).primesOver
      ↥(integralClosure ↥(placeBelow φ q) W.FunctionField))) :
    (heightOneOfPrimesOver P).asIdeal = P.1 := rfl

include hφint in
/-- **The `primesOver` ↔ fibre dictionary.**

The primes of the integral closure of the place below `q` that lie over its maximal ideal are in
bijection with the points of the projective curve contracting to `q`.  This is the index-set
translation `Ideal.sum_ramification_inertia_eq_finrank` needs: it sums over the left-hand side,
whereas `∑_{p ↦ q} e_p · f_p` is a sum over the right. -/
noncomputable def primesOverEquivFibre :
    ↥((IsLocalRing.maximalIdeal ↥(placeBelow φ q)).primesOver
        ↥(integralClosure ↥(placeBelow φ q) W.FunctionField))
      ≃ ↥(comapProjPoint hφF hφint ⁻¹' {q}) :=
  Equiv.ofBijective
    (fun P => ⟨projPointOfHeightOne φ hφF q (heightOneOfPrimesOver P),
      (comapProjPoint_projPointOfHeightOne_eq_iff hφF hφint _).2 P.2.2.over.symm⟩)
    ⟨fun P P' h => by
        have h' : projPointOfHeightOne φ hφF q (heightOneOfPrimesOver P)
            = projPointOfHeightOne φ hφF q (heightOneOfPrimesOver P') := congrArg Subtype.val h
        exact Subtype.ext (congrArg HeightOneSpectrum.asIdeal
          (projPointOfHeightOne_injective hφF h')),
      fun p => by
        obtain ⟨v, hv⟩ := exists_projPointOfHeightOne_eq hφF hφint p.2
        refine ⟨⟨v.asIdeal, v.isPrime, ⟨?_⟩⟩, Subtype.ext ?_⟩
        · exact ((comapProjPoint_projPointOfHeightOne_eq_iff hφF hφint v).1 (hv ▸ p.2)).symm
        · exact (congrArg (projPointOfHeightOne φ hφF q) (HeightOneSpectrum.ext rfl)).trans hv⟩

@[simp]
theorem primesOverEquivFibre_apply_coe
    (P : ↥((IsLocalRing.maximalIdeal ↥(placeBelow φ q)).primesOver
      ↥(integralClosure ↥(placeBelow φ q) W.FunctionField))) :
    (primesOverEquivFibre hφF hφint P : ProjPoint W)
      = projPointOfHeightOne φ hφF q (heightOneOfPrimesOver P) := rfl

include hφint in
/-- **The fibre is nonempty.**  `B` is integral over the place below, so *some* prime lies over its
maximal ideal (`Ideal.nonempty_primesOver`), and the dictionary carries it to a point.

This is the first consequence of the dictionary that the Weil-pairing front wants, and it needs no
part of the fundamental identity: "`[2]` is surjective on places" is already here. -/
theorem nonempty_fibre_comapProjPoint :
    (comapProjPoint hφF hφint ⁻¹' {q}).Nonempty := by
  haveI : Algebra.IsIntegral ↥(placeBelow φ q)
      ↥(integralClosure ↥(placeBelow φ q) W.FunctionField) :=
    IsIntegralClosure.isIntegral_algebra ↥(placeBelow φ q) W.FunctionField
  haveI : FaithfulSMul ↥(placeBelow φ q)
      ↥(integralClosure ↥(placeBelow φ q) W.FunctionField) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 fun x y h => Subtype.ext (Subtype.ext (by
      have hx := IsScalarTower.algebraMap_apply ↥(placeBelow φ q)
        ↥(integralClosure ↥(placeBelow φ q) W.FunctionField) W.FunctionField x
      have hy := IsScalarTower.algebraMap_apply ↥(placeBelow φ q)
        ↥(integralClosure ↥(placeBelow φ q) W.FunctionField) W.FunctionField y
      change algebraMap ↥(placeBelow φ q) W.FunctionField x
        = algebraMap ↥(placeBelow φ q) W.FunctionField y
      rw [hx, hy, h]))
  obtain ⟨P⟩ := (inferInstance : Nonempty ↥((IsLocalRing.maximalIdeal ↥(placeBelow φ q)).primesOver
    ↥(integralClosure ↥(placeBelow φ q) W.FunctionField)))
  exact ⟨_, (primesOverEquivFibre hφF hφint P).2⟩

include hφF hφint in
/-- **There are only finitely many primes over the maximal ideal of the place below.**  The fibre of
`comapProjPoint φ` is finite (`#675`), and the dictionary transports that.

This is the third hypothesis of `Ideal.sum_ramification_inertia_eq_finrank`, `[Fintype
(p.primesOver S)]`, in its `Finite` form; the `Fintype` it wants is `Fintype.ofFinite` and is
noncomputable, so it belongs in a `haveI` at the use site rather than in a statement. -/
theorem finite_primesOver_maximalIdeal_placeBelow :
    Finite ↥((IsLocalRing.maximalIdeal ↥(placeBelow φ q)).primesOver
      ↥(integralClosure ↥(placeBelow φ q) W.FunctionField)) := by
  haveI : Finite ↥(comapProjPoint hφF hφint ⁻¹' {q}) :=
    (finite_comapProjPoint_preimage_singleton hφF hφint q).to_subtype
  exact (primesOverEquivFibre hφF hφint).finite_iff.2 inferInstance

end Dedekind


/-! ### The `[2]∗` instantiation

Everything above is stated for an arbitrary `φ` fixing `F` with `F(W)` integral over its image, so
`[3]∗` and general `[n]∗` will use it unchanged.  Here it is specialised to `[2]∗`, where the
separability hypothesis is the one `#754` isolated: free in characteristic zero, and carried
explicitly otherwise.  The names follow `#754`'s `placeBelowTwo` layer. -/

namespace CoordinateRing

variable [W.IsElliptic] (h2 : (2 : F) ≠ 0)
  (hsep : Algebra.IsSeparable ↥(mulByTwoEndo (W := W) h2).fieldRange W.FunctionField)
  (q : ProjPoint W)

include hsep in
/-- **The `primesOver` ↔ fibre dictionary for `[2]∗`.**  The primes of the integral closure of the
place of `[2]∗F(W)` below `q` that lie over its maximal ideal are in bijection with the points of
the projective curve that `[2]` sends to `q`. -/
noncomputable def primesOverEquivFibreTwo :
    ↥((IsLocalRing.maximalIdeal ↥(placeBelowTwo W h2 q)).primesOver
        ↥(integralClosure ↥(placeBelowTwo W h2 q) W.FunctionField))
      ≃ ↥(comapProjPointTwo h2 ⁻¹' {q}) :=
  haveI := module_finite_mulByTwoEndoFieldRange (W := W) h2
  haveI := hsep
  primesOverEquivFibre (mulByTwoEndo_algebraMap_base h2) (mulByTwoEndo_isIntegralElem h2)

include hsep in
/-- **The fibre of `[2]` over a place is nonempty.**  Every place of `[2]∗F(W)` is the contraction
of a place of `F(W)`; classically, `[2]` is surjective on places.

This is the consequence of the dictionary that does not need the fundamental identity, and it is
what the Weil-pairing front asks for first. -/
theorem nonempty_fibre_comapProjPointTwo : ((comapProjPointTwo (W := W) h2) ⁻¹' {q}).Nonempty :=
  haveI := module_finite_mulByTwoEndoFieldRange (W := W) h2
  haveI := hsep
  nonempty_fibre_comapProjPoint (mulByTwoEndo_algebraMap_base h2) (mulByTwoEndo_isIntegralElem h2)

include hsep in
/-- **Finitely many primes lie over the maximal ideal of a place of `[2]∗F(W)`.**  The `Fintype`
`Ideal.sum_ramification_inertia_eq_finrank` asks for is `Fintype.ofFinite` of this, and is
noncomputable — keep it in a `haveI` at the use site. -/
theorem finite_primesOver_maximalIdeal_placeBelowTwo :
    Finite ↥((IsLocalRing.maximalIdeal ↥(placeBelowTwo W h2 q)).primesOver
      ↥(integralClosure ↥(placeBelowTwo W h2 q) W.FunctionField)) :=
  haveI := module_finite_mulByTwoEndoFieldRange (W := W) h2
  haveI := hsep
  finite_primesOver_maximalIdeal_placeBelow (mulByTwoEndo_algebraMap_base h2)
    (mulByTwoEndo_isIntegralElem h2)

/-- **The dictionary in characteristic zero, unconditionally**, off `#754`'s
`isSeparable_mulByTwoEndoFieldRange`.

⚠️ `nolint defsWithUnderscore` (`#1277`): `_of_charZero` is the hypothesis-naming convention the
theorems around it use, and the `def` is named to match them. -/
@[nolint defsWithUnderscore]
noncomputable def primesOverEquivFibreTwo_of_charZero [CharZero F] :
    ↥((IsLocalRing.maximalIdeal ↥(placeBelowTwo W h2 q)).primesOver
        ↥(integralClosure ↥(placeBelowTwo W h2 q) W.FunctionField))
      ≃ ↥(comapProjPointTwo h2 ⁻¹' {q}) :=
  primesOverEquivFibreTwo h2 (isSeparable_mulByTwoEndoFieldRange h2) q

/-- **The fibre of `[2]` is nonempty in characteristic zero, unconditionally.** -/
theorem nonempty_fibre_comapProjPointTwo_of_charZero [CharZero F] :
    ((comapProjPointTwo (W := W) h2) ⁻¹' {q}).Nonempty :=
  nonempty_fibre_comapProjPointTwo h2 (isSeparable_mulByTwoEndoFieldRange h2) q

/-! ### Non-vacuity

`primesOverEquivFibre` is built by `Equiv.ofBijective` out of `placeEquiv.symm`, itself extracted
from an existence statement by choice, and both of its halves rest on instance searches through the
`ValuationSubring`-of-a-`Subfield` stack that `#754` found to be delicate.  A curve on which the
whole chain elaborates with nothing supplied by hand is therefore committed rather than quoted.

`y² = x³ - x` over `ℚ` is the certificate curve of `PlacePullback.lean`, `PlaceResidueField.lean`,
`PlaceResidueComap.lean`, `PlaceDiscreteValuationRing.lean` and `PlaceBelowIntegralClosure.lean`,
and `ℚ` has characteristic zero, which is what makes the unconditional forms applicable. -/

section Nonvacuity

/-! The certificate curve `y² = x³ − x` is the shared `EllipticCurves.Fixture.y2EqX3SubX`, whose
single `[CharZero F]` instance also supplies `IsElliptic` here. -/

open EllipticCurves.Fixture

private lemma exampleTwoNeZero : (2 : ℚ) ≠ 0 := by norm_num

/-- **The dictionary on a curve that exists**, with the separability hypothesis supplied by the
tree rather than assumed. -/
noncomputable example (q : ProjPoint (y2EqX3SubX ℚ)) :
    ↥((IsLocalRing.maximalIdeal ↥(placeBelowTwo (y2EqX3SubX ℚ) exampleTwoNeZero q)).primesOver
        ↥(integralClosure ↥(placeBelowTwo (y2EqX3SubX ℚ) exampleTwoNeZero q)
          (y2EqX3SubX ℚ).FunctionField))
      ≃ ↥(comapProjPointTwo exampleTwoNeZero ⁻¹' {q}) :=
  primesOverEquivFibreTwo_of_charZero exampleTwoNeZero q

/-- **The fibre is nonempty on a curve that exists.**  This is the certificate that makes the
dictionary non-vacuous: an equivalence of two empty types would prove nothing. -/
example (q : ProjPoint (y2EqX3SubX ℚ)) :
    ((comapProjPointTwo (W := y2EqX3SubX ℚ) exampleTwoNeZero) ⁻¹' {q}).Nonempty :=
  nonempty_fibre_comapProjPointTwo_of_charZero exampleTwoNeZero q

/-- Finiteness of the index set, on the same curve. -/
example (q : ProjPoint (y2EqX3SubX ℚ)) :
    Finite ↥((IsLocalRing.maximalIdeal ↥(placeBelowTwo (y2EqX3SubX ℚ) exampleTwoNeZero
        q)).primesOver
      ↥(integralClosure ↥(placeBelowTwo (y2EqX3SubX ℚ) exampleTwoNeZero q)
        (y2EqX3SubX ℚ).FunctionField)) :=
  finite_primesOver_maximalIdeal_placeBelowTwo exampleTwoNeZero
    (isSeparable_mulByTwoEndoFieldRange exampleTwoNeZero) q

/-- The point at infinity is in the fibre over its own contraction, so that fibre is nonempty for a
reason that can be checked by hand — `#670` gives `comapProjPointTwo h2 none = none`. -/
example : (none : ProjPoint (y2EqX3SubX ℚ))
    ∈ (comapProjPointTwo (W := y2EqX3SubX ℚ) exampleTwoNeZero) ⁻¹' {none} :=
  comapProjPointTwo_none exampleTwoNeZero

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
