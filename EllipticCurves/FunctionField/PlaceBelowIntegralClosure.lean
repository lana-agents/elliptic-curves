/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByTwoDegree
import EllipticCurves.FunctionField.PlaceDiscreteValuationRing
import EllipticCurves.FunctionField.PlaceResidueComap
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# The place below, and the integral closure of `F(W)` over it

`EllipticCurves.FunctionField.PlacePullback` (`#668`) contracts a place of `F(W)` along an
`F`-embedding `φ : F(W) → F(W)` with `F(W)` integral over the image, and
`EllipticCurves.FunctionField.PlaceResidueComap` (`#744`) reads off the residue degree.  Both work
entirely inside `F(W)`: the place *of the subfield* `L = φ F(W)` is never named as a ring, because
`comapProjPoint φ p` is a point of `ProjPoint W` and its place is a valuation subring of `F(W)`.

The fundamental identity needs it named.  `#744`'s route decision settled on

```lean
-- Mathlib/RingTheory/RamificationInertia/Basic.lean
theorem Ideal.sum_ramification_inertia_eq_finrank
    [IsDomain R] [Module.Finite R S] [Module.Flat R S] [Fintype (p.primesOver S)] :
    ∑ q : p.primesOver S, q.1.ramificationIdx R * q.1.inertiaDeg R = Module.finrank R S
```

with `R` the valuation ring of a place of `L` and `S` its integral closure in `F(W)`, and named
three prerequisites.  `#753` discharged the first.  **This file discharges the second**:
`Module.Finite R S` and `Module.Flat R S`.

## The encoding, and the alternative that does not work

`placeBelow φ q` is a `ValuationSubring ↥φ.fieldRange` — a valuation ring of the **subfield**, not
of `F(W)`.  It is the image of `placeOf W q` under the isomorphism `φ.rangeRestrictFieldEquiv :
F(W) ≃+* ↥φ.fieldRange`, written as a `comap` along that isomorphism's inverse so that
`ValuationSubring.comap` supplies `mem_or_inv_mem'` for free.

The obvious alternative is to keep `↥(placeOf W q)` as the base ring and give it a *`φ`-twisted*
algebra structure on `F(W)`, never naming a subring of `L`.  **That does not work**, and the
obstruction is not stylistic: `Algebra ↥(placeOf W q) F(W)` is **already an instance** — a
valuation subring is a subring, and `Subring.toAlgebra` fires — with the algebra map the
*inclusion*.  A second instance
with algebra map `φ ∘ inclusion` would be a genuine diamond on a type where both are in scope, and
whichever won would silently change the meaning of `integralClosure ↥(placeOf W q) F(W)`.  Naming
the subring of `L` keeps every algebra map in sight an honest inclusion.

Working in `L` also makes deliverables that would otherwise be work into instance search:
`IsFractionRing (placeBelow φ q) L` and `IsIntegrallyClosed (placeBelow φ q)` are Mathlib instances
on **every** `ValuationSubring` of a field, and `IsLocalRing` and `IsDomain` come with them.  What
is *not* free is discreteness — that is `#753`, transported along `placeBelowEquiv`.

## Main results

* **`WeierstrassCurve.Affine.placeBelow`** — the valuation ring of the place of `L = φ F(W)` below,
  with `placeBelowEquiv : ↥(placeOf W q) ≃+* ↥(placeBelow φ q)` the transport isomorphism;
* **`WeierstrassCurve.Affine.instIsDiscreteValuationRingPlaceBelow`** — it is a discrete valuation
  ring, off `#753` and `IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing`.  Hence
  `isNoetherianRing_placeBelow`, which is the hypothesis `IsIntegralClosure.finite` wants;
* `WeierstrassCurve.Affine.placeBelow_comapProjPoint` — **the encoding is the right one**: the place
  below `comapProjPoint φ p` is `(placeOf W p).comap L.subtype`, i.e. literally `L ∩ placeOf W p`.
  This is the lemma the assembly (`#755`) needs to match `primesOver` with the fibre;
* **`WeierstrassCurve.Affine.module_flat_integralClosure_placeBelow`** — flatness, with **no**
  separability and **no** finiteness hypothesis: a place below is a PID, hence Bezout, and the
  integral closure sits inside `F(W)`, hence is torsion-free;
* **`WeierstrassCurve.Affine.module_finite_integralClosure_placeBelow`** — module-finiteness, under
  `[Module.Finite ↥φ.fieldRange F(W)]` and `[Algebra.IsSeparable ↥φ.fieldRange F(W)]`;
* **`WeierstrassCurve.Affine.finrank_integralClosure_placeBelow`** — under the same hypotheses, the
  rank of the integral closure *equals the degree of the field extension*.  This was not asked for
  and turns out to be free from `IsIntegralClosure.rank`; at `[2]∗` it reads
  `finrank (placeBelowTwo W h2 q) (integralClosure …) = 4`, which is the **right-hand side of the
  fundamental identity at the ring level**, so the assembly never has to descend from the field
  degree by hand;
* `WeierstrassCurve.Affine.CoordinateRing.placeBelowTwo`,
  `module_finite_integralClosure_placeBelowTwo` and `finrank_integralClosure_placeBelowTwo` — the
  `[2]∗` instantiation, in characteristic zero unconditionally and in general under the separability
  hypothesis.

## Separability, which is the whole of the remaining hypothesis

`IsIntegralClosure.finite` needs `[Algebra.IsSeparable L F(W)]`, and there are **two** routes to it
in this tree, with incomparable hypotheses.  In characteristic zero it is free:
`Algebra.IsSeparable.of_integral` is a priority-100 instance under `[Algebra.IsIntegral L K]
[CharZero L]`, and `module_finite_mulByTwoEndoFieldRange` supplies the integrality, so
`isSeparable_mulByTwoEndoFieldRange` below needs only `[CharZero F]` transported to the subfield.
That route needs **no** algebraic closure, so it is the one to use over `ℚ` or a number field.

Over an algebraically closed base field it holds in **every** characteristic `≠ 2`, with no
`CharZero`: `isSeparable_mulByTwoEndoFieldRange_of_isAlgClosed`
(`EllipticCurves.FunctionField.MulByTwoGalois`, `#759`) realises `[2]∗F(W)` as the fixed field of
the translations by `E[2]` and closes the sandwich against `#682`'s degree `4` with Artin's theorem,
which additionally gives `IsGalois`.  It is stated for exactly the `Subfield` presentation the
theorems below take as a hypothesis, so it plugs in with a `haveI`.

That is why the `[2]∗` results below come in two forms — a `[CharZero F]` one and one carrying
`Algebra.IsSeparable` explicitly.  **What is still not available in either route** is the classical
isogeny-theoretic statement that `[2]` is separable *as an isogeny*, whose proof differentiates the
invariant differential; nothing here or in `#759` supplies the step from separability of the
extension to a count of `E[2]`.

## What is *not* here

* The `primesOver` ↔ fibre dictionary (`#755`,
  `EllipticCurves.FunctionField.PlacePrimesOverFibre`) and the fundamental identity
  `∑ e_p · f_p = 4` itself (`#763`,
  `EllipticCurves.FunctionField.PlaceRamificationInertia`).  The *left*-hand side is what is missing
  **here**: nothing in this file matches a prime of the integral closure with a point of the fibre
  of `comapProjPointTwo`, and nothing in this file relates Mathlib's `Ideal.ramificationIdx` and
  `Ideal.inertiaDeg` to `ramificationIdxTwo` and `residueDegreeTwo`.
  `placeBelow_comapProjPoint` is the hook the dictionary hangs on, and
  `finrank_integralClosure_placeBelow` is the right-hand side it is fired against.
* `IsDedekindDomain` of the integral closure, and route (a) of `#744`'s decision — `#421`'s
  `B = integralClosure ([2]∗F[W]) F(W)` is a **different** `B`, over the affine coordinate ring
  rather than over a place, and route (c) does not need it.
* Separability of `[2]` in characteristic `p`, as above; `[3]∗` and general `[n]∗`; `#E[n] = n²`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
* Stichtenoth, *Algebraic Function Fields and Codes*, III.1 (places of a subfield, and III.1.11).
-/

open IsDedekindDomain Module

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]
  {φ : W.FunctionField →+* W.FunctionField}

/-! ### The place below, as a valuation ring of the subfield -/

variable (φ) in
/-- **The valuation ring of the place of `L = φ F(W)` below `q`.**

`φ.rangeRestrictFieldEquiv : F(W) ≃+* L` is an isomorphism, because a ring hom out of a field is
injective; `placeBelow φ q` is the image of `placeOf W q` under it, written as the `comap` along its
inverse so that `ValuationSubring.comap` supplies the `mem_or_inv_mem'` field.

Being a `ValuationSubring` of a field is what makes `IsFractionRing`, `IsIntegrallyClosed`,
`IsLocalRing` and `IsDomain` free below; see the module docstring for why the `φ`-twisted algebra
structure on `↥(placeOf W q)` is not an alternative. -/
noncomputable def placeBelow (q : ProjPoint W) : ValuationSubring ↥φ.fieldRange :=
  (placeOf W q).comap (φ.rangeRestrictFieldEquiv.symm : ↥φ.fieldRange →+* W.FunctionField)

@[simp]
lemma mem_placeBelow_iff {q : ProjPoint W} {y : ↥φ.fieldRange} :
    y ∈ placeBelow φ q ↔ φ.rangeRestrictFieldEquiv.symm y ∈ placeOf W q := Iff.rfl

variable (φ) in
/-- **The place below is isomorphic to the place it is transported from.**  The underlying map is
`φ` itself, corestricted twice; injectivity and surjectivity are both definitional once the
membership condition of `placeBelow` is unfolded. -/
noncomputable def placeBelowEquiv (q : ProjPoint W) :
    ↥(placeOf W q) ≃+* ↥(placeBelow φ q) where
  toFun x := ⟨φ.rangeRestrictFieldEquiv (x : W.FunctionField), by
    change φ.rangeRestrictFieldEquiv.symm _ ∈ placeOf W q
    rw [RingEquiv.symm_apply_apply]
    exact x.2⟩
  invFun y := ⟨φ.rangeRestrictFieldEquiv.symm (y : ↥φ.fieldRange), y.2⟩
  left_inv _ := Subtype.ext (by simp)
  right_inv _ := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

@[simp]
lemma coe_placeBelowEquiv (q : ProjPoint W) (x : placeOf W q) :
    ((placeBelowEquiv φ q x : placeBelow φ q) : ↥φ.fieldRange)
      = φ.rangeRestrictFieldEquiv (x : W.FunctionField) := rfl

/-- **A place below is a discrete valuation ring.**  `#753` proves it for `placeOf W q`, and
`placeBelowEquiv` is a ring isomorphism, so `IsDiscreteValuationRing.RingEquivClass` transports it.

This is the instance the rest of the file runs on: `IsNoetherianRing` — the hypothesis
`IsIntegralClosure.finite` wants — and `IsPrincipalIdealRing`, hence `IsBezout`, which is what
makes flatness cheap, are both downstream of it. -/
instance instIsDiscreteValuationRingPlaceBelow (q : ProjPoint W) :
    IsDiscreteValuationRing ↥(placeBelow φ q) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (placeBelowEquiv φ q)

/-- **A place below is Noetherian**, off the discrete valuation ring instance.  Named because this
is the hypothesis `IsIntegralClosure.finite` asks for — it is what `#744`'s route decision called
prerequisite (c-i), and what `#753` was filed to supply. -/
theorem isNoetherianRing_placeBelow (q : ProjPoint W) :
    IsNoetherianRing ↥(placeBelow φ q) := inferInstance

/-- **The subfield is the fraction field of the place below.**  Free: this holds for every
`ValuationSubring` of a field, and it is the reason the encoding puts the ring inside `L`. -/
theorem isFractionRing_placeBelow (q : ProjPoint W) :
    IsFractionRing ↥(placeBelow φ q) ↥φ.fieldRange := inferInstance

/-- **A place below is integrally closed.**  Free, for the same reason. -/
theorem isIntegrallyClosed_placeBelow (q : ProjPoint W) :
    IsIntegrallyClosed ↥(placeBelow φ q) := inferInstance

/-! ### The tower `placeBelow φ q → L → F(W)` -/

variable (φ) in
/-- The place below acts on `F(W)` through the subfield: the algebra map is the composite of two
inclusions, and nothing here is twisted by `φ`. -/
noncomputable instance instAlgebraPlaceBelow (q : ProjPoint W) :
    Algebra ↥(placeBelow φ q) W.FunctionField :=
  ((algebraMap (↥φ.fieldRange) W.FunctionField).comp
    (algebraMap ↥(placeBelow φ q) ↥φ.fieldRange)).toAlgebra

instance instIsScalarTowerPlaceBelow (q : ProjPoint W) :
    IsScalarTower ↥(placeBelow φ q) ↥φ.fieldRange W.FunctionField :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-! ### The encoding is the classical one

`placeBelow φ (comapProjPoint φ p)` is `L ∩ placeOf W p`, the classical valuation ring of the place
of the subfield below `p`.  This is the compatibility the assembly (`#755`) consumes: it is what
lets a prime of the integral closure lying over the maximal ideal of `placeBelow φ q` be matched
with a point of the fibre of `comapProjPoint φ` over `q`. -/

variable (hφF : ∀ c : F, φ (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c)
  (hφint : ∀ z : W.FunctionField, φ.IsIntegralElem z)

include hφF hφint in
/-- **The place below a contraction is the intersection with the subfield.**  Unfolding both sides,
`y ∈ L` lies in `placeBelow φ (comapProjPoint φ p)` iff `φ (φ⁻¹ y) = y` lies in `placeOf W p` — the
inverse cancels and no ramification theory is used. -/
theorem placeBelow_comapProjPoint (p : ProjPoint W) :
    placeBelow φ (comapProjPoint hφF hφint p)
      = (placeOf W p).comap (φ.fieldRange.subtype : ↥φ.fieldRange →+* W.FunctionField) := by
  ext y
  rw [mem_placeBelow_iff, mem_placeOf_comapProjPoint, ValuationSubring.mem_comap]
  exact Iff.of_eq (congrArg (· ∈ placeOf W p)
    (congrArg Subtype.val (φ.rangeRestrictFieldEquiv.apply_symm_apply y)))

/-! ### Flatness, which needs no separability -/

/-- **`F(W)` is torsion-free over a place below.**  The algebra map is a composite of two subring
inclusions, hence injective, and `F(W)` is a field, so a regular scalar acts injectively.

Stated by hand rather than reached through `Module.IsTorsionFree.trans_faithfulSMul`, whose
instance search exhausts its heartbeats on this type; the direct proof is four lines. -/
instance instIsTorsionFreePlaceBelow (q : ProjPoint W) :
    Module.IsTorsionFree ↥(placeBelow φ q) W.FunctionField where
  isSMulRegular r hr x y hxy := by
    have hinj : Function.Injective (algebraMap ↥(placeBelow φ q) W.FunctionField) :=
      Subtype.val_injective.comp Subtype.val_injective
    have hr0 : algebraMap ↥(placeBelow φ q) W.FunctionField r ≠ 0 := fun h =>
      hr.ne_zero (hinj (by rw [h, map_zero]))
    simp only [Algebra.smul_def] at hxy
    exact mul_left_cancel₀ hr0 hxy

/-- **The integral closure of a place below is flat over it.**

No separability and no finiteness hypothesis: `placeBelow φ q` is a discrete valuation ring
(`#753`), hence a principal ideal ring, hence Bezout; and the integral closure sits inside the field
`F(W)`, hence is torsion-free.  Over a Bezout domain torsion-free is *equivalent* to flat
(`Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`).

This is the second of the two module-theoretic hypotheses of
`Ideal.sum_ramification_inertia_eq_finrank`, and it is the cheap one — `#744`'s route decision said
so, and this is the statement that stops it being priced again.

⚠️ The Bezout route is taken rather than the `Flat` instance Mathlib registers for a Dedekind
domain with no torsion.  That instance exists and both of its hypotheses hold here — a place below
*is* a Dedekind domain, by `IsPrincipalIdealRing.isDedekindDomain` — but instance *search* for
`Flat` on this type exhausts its heartbeats.  Naming the equivalence costs two lines and avoids a
`set_option`. -/
theorem module_flat_integralClosure_placeBelow (q : ProjPoint W) :
    Module.Flat ↥(placeBelow φ q) ↥(integralClosure ↥(placeBelow φ q) W.FunctionField) := by
  haveI : Module.IsTorsionFree ↥(placeBelow φ q)
      ↥(integralClosure ↥(placeBelow φ q) W.FunctionField) :=
    IsIntegralClosure.isTorsionFree ↥(placeBelow φ q) W.FunctionField
  exact Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)

/-! ### Module-finiteness, which needs separability -/

/-- **The integral closure of a place below is module-finite over it**, given that `F(W)` is a
finite *separable* extension of the subfield.

This is `IsIntegralClosure.finite` with every one of its hypotheses supplied: `IsIntegrallyClosed`
and `IsFractionRing` are free from the `ValuationSubring` encoding, `IsNoetherianRing` is `#753`
transported along `placeBelowEquiv`, and the two hypotheses of the statement are the two that are
genuinely about the extension.  See the module docstring for why separability is a hypothesis here
and not a theorem. -/
theorem module_finite_integralClosure_placeBelow (q : ProjPoint W)
    [Module.Finite ↥φ.fieldRange W.FunctionField]
    [Algebra.IsSeparable ↥φ.fieldRange W.FunctionField] :
    Module.Finite ↥(placeBelow φ q) ↥(integralClosure ↥(placeBelow φ q) W.FunctionField) :=
  IsIntegralClosure.finite ↥(placeBelow φ q) ↥φ.fieldRange W.FunctionField _

/-- **The rank of the integral closure is the degree of the extension.**  Free from
`IsIntegralClosure.rank` once the same hypotheses are in place: a place below is a principal ideal
ring (`#753`) and `F(W)` is torsion-free over it, so the integral closure is a free module and its
rank can be read off after localising.

This is the *right-hand side* of `Ideal.sum_ramification_inertia_eq_finrank`, delivered in the shape
the assembly (`#755`) needs: with the general theorem instantiated at `[2]∗` it says
`finrank (placeBelowTwo W h2 q) (integralClosure …) = 4`, so the assembly never has to descend from
the field degree to the ring degree by hand. -/
theorem finrank_integralClosure_placeBelow (q : ProjPoint W)
    [Module.Finite ↥φ.fieldRange W.FunctionField]
    [Algebra.IsSeparable ↥φ.fieldRange W.FunctionField] :
    finrank ↥(placeBelow φ q) ↥(integralClosure ↥(placeBelow φ q) W.FunctionField)
      = finrank ↥φ.fieldRange W.FunctionField :=
  IsIntegralClosure.rank ↥(placeBelow φ q) ↥φ.fieldRange W.FunctionField _

/-! ### The `[2]∗` instantiation

`L = ↥(mulByTwoEndo h2).fieldRange` is the same subset of `F(W)` as the `RingHom.range` that
`MulByTwoDegree` and `MulByTwoExtensionFinite` state their results for — membership is `Iff.rfl` —
but it is a `Subfield` rather than a `Subring`, which is what makes it a `Field` by instance search
and hence what lets `ValuationSubring L` be written at all.  `rangeEquivFieldRangeTwo` is the
transport, and it is the identity on elements. -/

namespace CoordinateRing

/-- The identity map, read as an isomorphism from the `RingHom.range` of `[2]∗` to its
`fieldRange`.  Both are the same subset of `F(W)` — `mem_fieldRange` and `mem_range` are literally
the same statement — but they live in different subobject lattices, so the results of
`MulByTwoDegree` have to be carried across. -/
def rangeEquivFieldRangeTwo (h2 : (2 : F) ≠ 0) :
    ↥(mulByTwoEndo (W := W) h2).range ≃+* ↥(mulByTwoEndo (W := W) h2).fieldRange where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

omit [IsDedekindDomain W.CoordinateRing] in
/-- **`[F(W) : [2]∗F(W)] = 4`, for the subfield.**  `finrank_mulByTwoRange_functionField` (`#682`)
in the `Subfield` presentation this file needs. -/
theorem finrank_mulByTwoEndoFieldRange [W.IsElliptic] (h2 : (2 : F) ≠ 0) :
    finrank ↥(mulByTwoEndo (W := W) h2).fieldRange W.FunctionField = 4 := by
  letI : Algebra ↥(mulByTwoEndo (W := W) h2).range W.FunctionField :=
    ((mulByTwoEndo (W := W) h2).range.subtype).toAlgebra
  rw [← Algebra.finrank_eq_of_equiv_equiv (rangeEquivFieldRangeTwo h2)
    (RingEquiv.refl W.FunctionField) (by ext a; rfl)]
  exact finrank_mulByTwoRange_functionField h2

omit [IsDedekindDomain W.CoordinateRing] in
/-- **`F(W)` is a finite extension of the subfield `[2]∗F(W)`**, off the degree being `4 ≠ 0`. -/
theorem module_finite_mulByTwoEndoFieldRange [W.IsElliptic] (h2 : (2 : F) ≠ 0) :
    Module.Finite ↥(mulByTwoEndo (W := W) h2).fieldRange W.FunctionField :=
  Module.finite_of_finrank_pos (by rw [finrank_mulByTwoEndoFieldRange h2]; norm_num)

omit [IsDedekindDomain W.CoordinateRing] in
/-- **In characteristic zero, `F(W)` is separable over `[2]∗F(W)`.**

The extension is finite, hence integral, and `Algebra.IsSeparable.of_integral` is an instance for an
integral extension of a characteristic-zero field.  `CharZero` has to be transported twice: from `F`
to `F(W)` along the injective structure map, and from `F(W)` down to the subfield.

⚠️ This is the *only* thing in this file that fails in characteristic `p`, and it fails because it
is unproved there, not because it is false — see the module docstring. -/
theorem isSeparable_mulByTwoEndoFieldRange [W.IsElliptic] [CharZero F] (h2 : (2 : F) ≠ 0) :
    Algebra.IsSeparable ↥(mulByTwoEndo (W := W) h2).fieldRange W.FunctionField := by
  haveI : CharZero W.FunctionField :=
    charZero_of_injective_algebraMap (algebraMap F W.FunctionField).injective
  haveI : CharZero ↥(mulByTwoEndo (W := W) h2).fieldRange :=
    ((mulByTwoEndo (W := W) h2).fieldRange.subtype).charZero
  haveI := module_finite_mulByTwoEndoFieldRange (W := W) h2
  haveI : Algebra.IsIntegral ↥(mulByTwoEndo (W := W) h2).fieldRange W.FunctionField :=
    Algebra.IsIntegral.of_finite _ _
  infer_instance

variable (W) in
/-- **The valuation ring of the place of `[2]∗F(W)` below `q`.**  The `[2]∗` instantiation of
`placeBelow`; `placeBelowTwo_comapProjPointTwo` says it is `[2]∗F(W) ∩ placeOf W p` for every `p`
above `q`, which is the classical description. -/
noncomputable def placeBelowTwo (h2 : (2 : F) ≠ 0) (q : ProjPoint W) :
    ValuationSubring ↥(mulByTwoEndo (W := W) h2).fieldRange :=
  placeBelow (mulByTwoEndo h2) q

/-- **A place of `[2]∗F(W)` is a discrete valuation ring.**  `instIsDiscreteValuationRingPlaceBelow`
does not fire on `placeBelowTwo` by itself — that is a `def`, not an `abbrev`, so it is not
transparent to instance search — and every consumer of this file wants the instance rather than the
theorem, so it is restated at the `[2]∗` layer. `IsNoetherianRing` and `IsPrincipalIdealRing` follow
from it by search. -/
instance instIsDiscreteValuationRingPlaceBelowTwo (h2 : (2 : F) ≠ 0) (q : ProjPoint W) :
    IsDiscreteValuationRing ↥(placeBelowTwo W h2 q) :=
  instIsDiscreteValuationRingPlaceBelow q

/-- **`F(W)` is torsion-free over a place of `[2]∗F(W)`.**  Restated at the `[2]∗` layer for the
same reason as the discrete valuation ring instance: `placeBelowTwo` is opaque to instance
search. -/
instance instIsTorsionFreePlaceBelowTwo (h2 : (2 : F) ≠ 0) (q : ProjPoint W) :
    Module.IsTorsionFree ↥(placeBelowTwo W h2 q) W.FunctionField :=
  instIsTorsionFreePlaceBelow q

/-- The `[2]∗` form of `placeBelow_comapProjPoint`: the place of `[2]∗F(W)` below a place `p` of
`F(W)` is the intersection of `[2]∗F(W)` with `placeOf W p`. -/
theorem placeBelowTwo_comapProjPointTwo (h2 : (2 : F) ≠ 0) (p : ProjPoint W) :
    placeBelowTwo W h2 (comapProjPointTwo h2 p)
      = (placeOf W p).comap ((mulByTwoEndo (W := W) h2).fieldRange.subtype) :=
  placeBelow_comapProjPoint _ _ p

/-- **The integral closure of a place of `[2]∗F(W)` is flat over it.**  No hypothesis on the
characteristic and none on `F`: this is the general `module_flat_integralClosure_placeBelow`. -/
theorem module_flat_integralClosure_placeBelowTwo (h2 : (2 : F) ≠ 0) (q : ProjPoint W) :
    Module.Flat ↥(placeBelowTwo W h2 q)
      ↥(integralClosure ↥(placeBelowTwo W h2 q) W.FunctionField) :=
  module_flat_integralClosure_placeBelow q

/-- **`F(W)` is module-finite over a place of `[2]∗F(W)`, given separability.**  The general form,
with the one hypothesis that characteristic `p` does not supply carried explicitly. -/
theorem module_finite_integralClosure_placeBelowTwo [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    (hsep : Algebra.IsSeparable ↥(mulByTwoEndo (W := W) h2).fieldRange W.FunctionField)
    (q : ProjPoint W) :
    Module.Finite ↥(placeBelowTwo W h2 q)
      ↥(integralClosure ↥(placeBelowTwo W h2 q) W.FunctionField) := by
  haveI := module_finite_mulByTwoEndoFieldRange (W := W) h2
  haveI := hsep
  exact module_finite_integralClosure_placeBelow q

/-- **`F(W)` is module-finite over a place of `[2]∗F(W)`, in characteristic zero, unconditionally.**

This is the shape the assembly (`#755`) should consume first: together with
`module_flat_integralClosure_placeBelowTwo` it supplies both module-theoretic hypotheses of
`Ideal.sum_ramification_inertia_eq_finrank`, leaving only the `primesOver` ↔ fibre dictionary. -/
theorem module_finite_integralClosure_placeBelowTwo_of_charZero [W.IsElliptic] [CharZero F]
    (h2 : (2 : F) ≠ 0) (q : ProjPoint W) :
    Module.Finite ↥(placeBelowTwo W h2 q)
      ↥(integralClosure ↥(placeBelowTwo W h2 q) W.FunctionField) :=
  module_finite_integralClosure_placeBelowTwo h2 (isSeparable_mulByTwoEndoFieldRange h2) q

/-- **The integral closure of a place of `[2]∗F(W)` has rank `4` over it**, given separability.

The right-hand side of the fundamental identity, at the ring level: `#682` gives
`[F(W) : [2]∗F(W)] = 4` for the *fields*, and `finrank_integralClosure_placeBelow` carries it down
to the local rings.  This is the half of `sum_ramificationIdxTwo_mul_residueDegreeTwo`
(`EllipticCurves.FunctionField.PlaceRamificationInertia`, `#763`) that does not need the
`primesOver` ↔ fibre dictionary; that theorem consumes this one verbatim. -/
theorem finrank_integralClosure_placeBelowTwo [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    (hsep : Algebra.IsSeparable ↥(mulByTwoEndo (W := W) h2).fieldRange W.FunctionField)
    (q : ProjPoint W) :
    finrank ↥(placeBelowTwo W h2 q)
      ↥(integralClosure ↥(placeBelowTwo W h2 q) W.FunctionField) = 4 := by
  haveI := module_finite_mulByTwoEndoFieldRange (W := W) h2
  haveI := hsep
  exact (finrank_integralClosure_placeBelow (φ := mulByTwoEndo h2) q).trans
    (finrank_mulByTwoEndoFieldRange h2)

/-- **The rank is `4`, in characteristic zero, unconditionally.** -/
theorem finrank_integralClosure_placeBelowTwo_of_charZero [W.IsElliptic] [CharZero F]
    (h2 : (2 : F) ≠ 0) (q : ProjPoint W) :
    finrank ↥(placeBelowTwo W h2 q)
      ↥(integralClosure ↥(placeBelowTwo W h2 q) W.FunctionField) = 4 :=
  finrank_integralClosure_placeBelowTwo h2 (isSeparable_mulByTwoEndoFieldRange h2) q

/-! ### Non-vacuity

Every statement above carries `[IsDedekindDomain W.CoordinateRing]`, the `[2]∗` half adds
`[W.IsElliptic]` and `(2 : F) ≠ 0`, and the headline additionally wants `[CharZero F]`; on top of
that `placeBelow` is built from `placeOf`, which is itself extracted from an existence statement by
choice, and the ring `↥(placeBelowTwo W h2 q)` carries five instances that have to be found by
search.  A curve on which the whole chain elaborates with nothing supplied by hand is therefore
committed rather than quoted.

`y² = x³ - x` over `ℚ` has discriminant `64`, so `IsElliptic` alone gives the Dedekind instance; it
is the certificate curve of `PlacePullback.lean`, `PlaceResidueField.lean`, `PlaceResidueComap.lean`
and `PlaceDiscreteValuationRing.lean`, and `ℚ` has characteristic zero, which is exactly what makes
the unconditional form of the headline applicable here. -/

section Nonvacuity

/-- The curve `y² = x³ - x` over `ℚ`, of discriminant `64`. -/
private def exampleCurve : Affine ℚ := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleTwoNeZero : (2 : ℚ) ≠ 0 := by norm_num

/-- **The degree of `[2]` on a curve that exists**, in the `Subfield` presentation this file runs
on. -/
example : finrank ↥(mulByTwoEndo (W := exampleCurve) exampleTwoNeZero).fieldRange
    exampleCurve.FunctionField = 4 :=
  finrank_mulByTwoEndoFieldRange exampleTwoNeZero

/-- **A place of `[2]∗ℚ(W)` is a discrete valuation ring**, by instance search: `#753`'s instance
transported along `placeBelowEquiv`, with the `ValuationSubring` of a subfield in between. -/
example (q : ProjPoint exampleCurve) :
    IsDiscreteValuationRing ↥(placeBelowTwo exampleCurve exampleTwoNeZero q) := inferInstance

/-- And the four instances the fundamental identity will read off it, all by search. -/
example (q : ProjPoint exampleCurve) :
    IsNoetherianRing ↥(placeBelowTwo exampleCurve exampleTwoNeZero q) := inferInstance

example (q : ProjPoint exampleCurve) :
    IsIntegrallyClosed ↥(placeBelowTwo exampleCurve exampleTwoNeZero q) := inferInstance

example (q : ProjPoint exampleCurve) :
    IsFractionRing ↥(placeBelowTwo exampleCurve exampleTwoNeZero q)
      ↥(mulByTwoEndo (W := exampleCurve) exampleTwoNeZero).fieldRange := inferInstance

example (q : ProjPoint exampleCurve) :
    IsDomain ↥(placeBelowTwo exampleCurve exampleTwoNeZero q) := inferInstance

/-- **The headline on a curve that exists, with nothing discharged by hand.**  `ℚ` has
characteristic zero, so the separability hypothesis is supplied by the tree rather than assumed —
which is the point of certifying it here rather than on an algebraically closed base field. -/
example (q : ProjPoint exampleCurve) :
    Module.Finite ↥(placeBelowTwo exampleCurve exampleTwoNeZero q)
      ↥(integralClosure ↥(placeBelowTwo exampleCurve exampleTwoNeZero q)
        exampleCurve.FunctionField) :=
  module_finite_integralClosure_placeBelowTwo_of_charZero exampleTwoNeZero q

/-- **The right-hand side of the fundamental identity, on a curve that exists**: the integral
closure of a place of `[2]∗ℚ(W)` has rank `4` over it. -/
example (q : ProjPoint exampleCurve) :
    finrank ↥(placeBelowTwo exampleCurve exampleTwoNeZero q)
      ↥(integralClosure ↥(placeBelowTwo exampleCurve exampleTwoNeZero q)
        exampleCurve.FunctionField) = 4 :=
  finrank_integralClosure_placeBelowTwo_of_charZero exampleTwoNeZero q

/-- Flatness on the same curve, which needs neither the characteristic nor ellipticity. -/
example (q : ProjPoint exampleCurve) :
    Module.Flat ↥(placeBelowTwo exampleCurve exampleTwoNeZero q)
      ↥(integralClosure ↥(placeBelowTwo exampleCurve exampleTwoNeZero q)
        exampleCurve.FunctionField) :=
  module_flat_integralClosure_placeBelowTwo exampleTwoNeZero q

/-- **The encoding is the classical one, on a curve that exists**: the place of `[2]∗ℚ(W)` below `p`
is the intersection of `[2]∗ℚ(W)` with the place at `p`. -/
example (p : ProjPoint exampleCurve) :
    placeBelowTwo exampleCurve exampleTwoNeZero (comapProjPointTwo exampleTwoNeZero p)
      = (placeOf exampleCurve p).comap
        ((mulByTwoEndo (W := exampleCurve) exampleTwoNeZero).fieldRange.subtype) :=
  placeBelowTwo_comapProjPointTwo exampleTwoNeZero p

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
