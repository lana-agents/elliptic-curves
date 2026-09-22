/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Galois.NormalClosureSeparable
import EllipticCurves.Torsion.ThreeTorsionStructure
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Normal.Closure

/-!
# The `3`-division field

For an elliptic curve `W` over a field `F` of characteristic `≠ 2, 3`, this file **constructs** a
finite separable extension of `F` over which the `3`-torsion is full — `#E[3] = 9` and
`E[3] ≃+ ZMod 3 × ZMod 3`.

`EllipticCurves.Torsion.ThreeTorsionStructure` proves both conclusions over any field satisfying
two conditions — `card_torsion_three_of_splits` and `nonempty_torsionThree_addEquiv_of_splits` —
and its `## What is *not* here` says in terms that no field is produced there, and why:

> ⚠️ **The `3`-division field.**  Nothing below constructs a field satisfying the two conditions,
> and — unlike at `n = 2` — no single polynomial's splitting field does: the second condition is
> about `Ψ₂Sq` at the roots of `Ψ₃`, so the field is `Ψ₃`'s splitting field followed by a tower of
> quadratics.

That is what this file supplies, and the quoted diagnosis is exactly right: the field below is a
**two-step tower** and not a splitting field.

## The mechanism

The two conditions are `hsplits : Ψ₃.Splits` and
`hsq : ∀ x, Ψ₃.eval x = 0 → IsSquare (Ψ₂Sq.eval x)`, and they are paid one layer each.

**Layer one, `L₁`** — a splitting field of `W.Ψ₃` over `F`. This is `hsplits` by construction, and
it is Galois over `F` because `Ψ₃` is separable. ⚠️
`EllipticCurves.Torsion.TwoTorsionSplittingField` records of `n = 3` that *"`Ψ₃` is a quartic and
not a cubic, so `Cubic.discr_ne_zero_iff_roots_nodup` does not reach it"*, and that is true and
does not matter: `nodup_roots_Ψ₃` is already closure-free
and holds over **every** field of characteristic `≠ 2, 3`, so applying it to `W⁄L` at a splitting
field `L` and feeding `Polynomial.nodup_aroots_iff_of_splits` gives `separable_Ψ₃` with no quartic
discriminant anywhere. **The `n = 3` separability is cheaper than the `n = 2` one, not dearer.**

**Layer two, `L₂`** — a splitting field over `L₁` of `Ψ₂SqRootPoly`, the product of `X² - C c` over
the `Finset` of **values** `c` that `(W⁄L₁).Ψ₂Sq` takes at the roots of `(W⁄L₁).Ψ₃`. Over `L₂` every
root of `(W⁄L₂).Ψ₃` is the image of a root `x` of `(W⁄L₁).Ψ₃` — `Ψ₃` splits over `L₁`, so
`Polynomial.Splits.roots_map` identifies the two root multisets — and `X² - C ((W⁄L₁).Ψ₂Sq.eval x)`
divides a polynomial that splits over `L₂`, hence splits there, hence has a root: that root is the
square root `hsq` asks for.

⚠️ **The product is over the values and not over the roots, and that is load-bearing.** Indexed by
the roots it repeats a factor whenever `Ψ₂Sq` takes one value at two of them, and a repeated factor
is not separable — which would cost `Algebra.IsSeparable L₁ L₂` and with it the only reason to build
the tower. Indexed by the image `Finset` the factors are pairwise coprime, since the difference of
two of them is the unit `C (d - c)`, and each is separable by `Polynomial.separable_X_pow_sub_C`
whose `a ≠ 0` side condition is discharged for free at a root of `Ψ₃` by
`Ψ₂Sq_eval_ne_zero_of_root_Ψ₃`.

## Main definitions

* `WeierstrassCurve.Affine.Ψ₂SqRootPoly`: the product of `X² - C c` over the values `c` taken by
  `Ψ₂Sq` at the roots of `Ψ₃`, whose splitting field is layer two.
* `WeierstrassCurve.Affine.threeDivisionField`: the tower, built at the canonical splitting fields.
* `WeierstrassCurve.Affine.threeDivisionGaloisField`: its normal closure over `F`, which is the
  Galois extension a descent argument consumes.

## Main statements

**The hypotheses the bullets omit**, keyed on the binders and not on the names.  ⚠️ **Re-scored
over all 26 statements** when `## The Galois closure` and the `_of_algHom` family were added, not
incremented from the earlier `nine / eighteen` reading.  **Fourteen** of the twenty-six statements
below take `[W.IsElliptic]`, and they are exactly the fourteen that take both `(2 : F) ≠ 0` and
`(3 : F) ≠ 0`: `separable_Ψ₃`, `isGalois_of_isSplittingField_Ψ₃`, `card_torsion_three_tower`,
`nonempty_torsionThree_addEquiv_tower`, `isGalois_tower_top`, `isSeparable_tower`, the two
`_of_algHom` counting statements, `isGalois_threeDivisionGaloisField`, the two
`_threeDivisionGaloisField` counting statements, and the three `threeDivisionField` statements
other than `finiteDimensional_threeDivisionField`.  `separable_Ψ₂SqRootPoly` is the same shape one
layer up: `[(W⁄L₁).IsElliptic]`, `(2 : L₁) ≠ 0` and `(3 : L₁) ≠ 0`.  **Three** take a
characteristic hypothesis alone and no ellipticity — `isSquare_Ψ₂Sq_eval_tower` and
`isSquare_Ψ₂Sq_eval_of_algHom` take `(3 : F) ≠ 0` and `dvd_Ψ₂SqRootPoly` takes `(3 : L₁) ≠ 0`.
⚠️ The remaining **eight** take none of them at all: `splits_Ψ₃_baseChange`, `splits_Ψ₃_tower`,
`splits_Ψ₃_of_algHom`, `Ψ₂SqRootPoly_ne_zero` and **all four** `finiteDimensional_*` —
`finiteDimensional_threeDivisionField` and `finiteDimensional_threeDivisionGaloisField` included,
which is why that family is not globbed here.  The **eight** counting statements additionally take
a `DecidableEq` instance on the field they count over: `[DecidableEq L₂]` for the two `_tower`
ones, `[DecidableEq (threeDivisionField W)]` for the two concrete ones, `[DecidableEq M]` for the
two `_of_algHom` ones and `[DecidableEq (threeDivisionGaloisField W)]` for the two over the Galois
closure.  The `_tower` statements take the tower `[Algebra F L₁] [Algebra L₁ L₂]
[IsScalarTower F L₁ L₂]` together with `[W.Ψ₃.IsSplittingField F L₁]` and
`[(Ψ₂SqRootPoly W L₁).IsSplittingField L₁ L₂]`, and name `L₁` explicitly because it does not occur
in their conclusions.  The `_of_algHom` statements take **no** instance relating `L` and `M`: the
`F`-algebra map is an explicit argument, which is what an `IntermediateField` can supply and a
scalar tower cannot.

* `WeierstrassCurve.Affine.separable_Ψ₃`: the `3`-division quartic is a separable polynomial.
* `WeierstrassCurve.Affine.splits_Ψ₃_baseChange`: `Ψ₃` of `W⁄L₁` splits.
* `WeierstrassCurve.Affine.isGalois_of_isSplittingField_Ψ₃`: `L₁ / F` is Galois.
* `WeierstrassCurve.Affine.finiteDimensional_of_isSplittingField_Ψ₃`: `L₁ / F` is finite.
* `WeierstrassCurve.Affine.Ψ₂SqRootPoly_ne_zero`, `WeierstrassCurve.Affine.dvd_Ψ₂SqRootPoly` and
  `WeierstrassCurve.Affine.separable_Ψ₂SqRootPoly`: layer two's polynomial is nonzero, is divisible
  by the quadratic at each root of `Ψ₃`, and is separable.
* `WeierstrassCurve.Affine.splits_Ψ₃_tower` and `WeierstrassCurve.Affine.isSquare_Ψ₂Sq_eval_tower`:
  the two conditions of `card_torsion_three_of_splits`, over `L₂`.
* `WeierstrassCurve.Affine.card_torsion_three_tower`: `#E[3] = 9` over `L₂`.
* `WeierstrassCurve.Affine.nonempty_torsionThree_addEquiv_tower`: `E[3] ≃+ ZMod 3 × ZMod 3` over
  `L₂`.
* `WeierstrassCurve.Affine.finiteDimensional_tower`: `L₂ / F` is finite.
* `WeierstrassCurve.Affine.isGalois_tower_top`: `L₂ / L₁` is Galois.
* `WeierstrassCurve.Affine.isSeparable_tower`: `L₂ / F` is separable.
* `card_torsion_three_threeDivisionField`, `nonempty_torsionThree_addEquiv_threeDivisionField`,
  `finiteDimensional_threeDivisionField` and `isSeparable_threeDivisionField`: the same four
  statements at `threeDivisionField W`, with no splitting-field instance left for the caller to
  supply.
* `WeierstrassCurve.Affine.splits_Ψ₃_of_algHom` and
  `WeierstrassCurve.Affine.isSquare_Ψ₂Sq_eval_of_algHom`: both conditions go up an arbitrary
  `F`-algebra map, the second given the first downstairs.
* `WeierstrassCurve.Affine.card_torsion_three_of_algHom` and
  `WeierstrassCurve.Affine.nonempty_torsionThree_addEquiv_of_algHom`: so both conclusions do.
* `WeierstrassCurve.Affine.isGalois_threeDivisionGaloisField` and
  `WeierstrassCurve.Affine.finiteDimensional_threeDivisionGaloisField`: the Galois closure is
  finite and **Galois** over `F`.
* `WeierstrassCurve.Affine.card_torsion_three_threeDivisionGaloisField` and
  `WeierstrassCurve.Affine.nonempty_torsionThree_addEquiv_threeDivisionGaloisField`: `#E[3] = 9`
  and `E[3] ≃+ ZMod 3 × ZMod 3` over it.

## What is *not* here

* ⚠️ **`IsGalois F L₂`, and it is not an omission — it is false in general.** `L₁ / F` and `L₂ / L₁`
  are both Galois, and Galois is not transitive: `L₂ / F` is finite and separable but need not be
  normal. What a descent argument wants is therefore built here in two pieces rather than one —
  `finiteDimensional_tower` and `isSeparable_tower` are exactly the hypotheses under which the
  normal closure of `L₂ / F` is Galois. ⚠️ **This bullet used to close *"Nothing below forms that
  normal closure"*, and that clause is retired**: `## The Galois closure` forms it and
  `isGalois_threeDivisionGaloisField` is the conclusion. ⚠️ **The statement about `L₂` itself is
  unchanged and is still not here** — no statement below says `IsGalois F L₂`, because it is false.
* ⚠️ **A Galois closure at a general `L₂`.** `threeDivisionGaloisField` is formed only at the
  concrete `threeDivisionField W`; there is no `_tower` form of it, because the normal closure has
  to be taken inside a named ambient field and the `_tower` section's `L₂` comes with none.
  Nothing below states the general form, in either direction.
* **The descent itself.** `#962` records the `hprin` gate at `n = 3`; this file supplies two of its
  inputs — a field over which `E[3]` is full, and a **Galois** such field — and no statement below
  mentions a divisor, a place or a principal divisor. ⚠️ Nothing here closes that ledger row: the
  `n = 3` analogues of the halving extension and of the cocycle argument are untouched.
* **Any statement about the degree `[L₂ : F]`.** The construction gives finiteness and nothing
  sharper; in particular nothing below says the tower is proper at layer two, only that layer one
  is proper for the certificate curve.
* **`n = 2`.** `EllipticCurves.Torsion.TwoTorsionSplittingField` is the `n = 2` layer and is
  untouched; nothing below is stated at a general index, and the second layer has no `n = 2`
  counterpart at all, because a `2`-torsion point is its own `x`-coordinate and there is no `y` to
  solve for. ⚠️ The `n = 2` counterpart of `## The Galois closure` is a **different** construction
  and not an instance of anything below: at `n = 2` the extension whose normal closure is taken is
  a halving tower over the `2`-division field (`EllipticCurves.Torsion.HalvingExtension`), and
  `EllipticCurves.Torsion.HalvingGaloisTower` is where it is built (`#2161`, landed at `f263f90`).
* **Characteristic `2` or `3`.** Every statement that mentions the torsion carries `(2 : F) ≠ 0`
  and `(3 : F) ≠ 0`, and nothing below decides anything in either characteristic.

## Non-vacuity

The `Nonvacuity` section certifies over `ℚ` on the shared fixture
`EllipticCurves.Fixture.y2AddYEqX3` — which `EllipticCurves.Fixtures` already names *"this tree's
standard `n = 3` certificate curve"* — that layer one is a **proper** extension: `Ψ₃ = 3X⁴ + 3X`
factors as `3X(X + 1)(X² - X + 1)` whose last factor is positive over `ℚ`, so `Ψ₃` has exactly `2`
rational roots against the `4` that `card_roots_Ψ₃_of_splits` would force, and it does not split
over `ℚ`. The `9` is then certified at `threeDivisionField (y2AddYEqX3 ℚ)`.

Over `threeDivisionGaloisField (y2AddYEqX3 ℚ)` the section certifies `IsGalois ℚ` and the same `9`
— ⚠️ **two** theorems and not three, because the not-splitting certificate is not re-run there
and **could not be**: `Ψ₃` splits over the closure, by `splits_Ψ₃_of_algHom` along the same
`IsScalarTower.toAlgHom` that `card_torsion_three_threeDivisionGaloisField` feeds itself. ⚠️ **They
certify the construction and not that the closure is proper over the tower**: nothing below
computes `[L₂ : F]` or compares it with the degree of the closure, so the case
`threeDivisionGaloisField W = threeDivisionField W` is not excluded for this curve or for any
other. What the `ℚ` base does exclude is the degenerate case at the **bottom**, `L₁ = F`.

⚠️ **A rational base is not vacuous here, and that is the opposite of the `_of_splits` layer's
situation.** `ThreeTorsionStructure`'s `## What is *not* here` argues that its two hypotheses force
`μ₃ ⊆ F` and so cannot both hold over `ℚ`, which is why `#2105`'s certificate for them needs a
finite base. The statements below certify the **construction**, whose entire content is that `ℚ` is
too small — so `ℚ` is the right base for them and a base over which `Ψ₃` already split would leave
everything green and certify only the case `L₁ = F`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7 (the division fields
  `K(E[m])` and their Galois representations).
-/

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-- A numeral that is nonzero in `F` stays nonzero in a field extension `L`.  ⚠️ Duplicated on
purpose: `EllipticCurves.Torsion.TwoTorsionSplittingField` carries the `2` case of this under the
name `algebraMap_two_ne_zero` and it is `private` there, and the general-numeral form
`EllipticCurves.FunctionField.FunctionFieldBaseChange.algebraMap_ofNat_ne_zero` is downstream of
`Torsion/`, so neither can be cited from here. -/
private lemma algebraMap_ofNat_ne_zero {L : Type*} [Field L] [Algebra F L] (n : ℕ) [n.AtLeastTwo]
    (h : (OfNat.ofNat n : F) ≠ 0) : (OfNat.ofNat n : L) ≠ 0 := by
  rw [← map_ofNat (algebraMap F L) n, ne_eq, map_eq_zero]
  exact h

/-- **The `3`-division quartic is a separable polynomial** for an elliptic curve over a field of
characteristic `≠ 2, 3`.

⚠️ **No quartic discriminant is involved, and none is available.**
`EllipticCurves.Torsion.TwoTorsionSplittingField` gets `separable_Ψ₂Sq` out of
`Cubic.discr_ne_zero_iff_roots_nodup` and says of `n = 3` that *"`Ψ₃` is a quartic and not a cubic,
so `Cubic.discr_ne_zero_iff_roots_nodup` does not reach it"*.  It does not have to: `nodup_roots_Ψ₃`
holds over **any** field of characteristic `≠ 2, 3` with no closure and no discriminant — its whole
content is that `Ψ₃' = 3Ψ₂Sq` and that a root of `Ψ₃` is not a root of `Ψ₂Sq` — so it applies to
`W⁄L` at a splitting field `L` of `Ψ₃`, and `Polynomial.nodup_aroots_iff_of_splits` turns *no
repeated root there* into separability of `Ψ₃` over `F`. -/
theorem separable_Ψ₃ [W.IsElliptic] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) : W.Ψ₃.Separable := by
  classical
  have hsplits : (W.Ψ₃.map (algebraMap F W.Ψ₃.SplittingField)).Splits :=
    IsSplittingField.splits W.Ψ₃.SplittingField W.Ψ₃
  refine (Polynomial.nodup_aroots_iff_of_splits (K := W.Ψ₃.SplittingField)
    (W.Ψ₃_ne_zero h3) hsplits).mp ?_
  haveI : (W⁄W.Ψ₃.SplittingField).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F W.Ψ₃.SplittingField)).IsElliptic
  have hnodup := nodup_roots_Ψ₃ (W := W⁄W.Ψ₃.SplittingField)
    (algebraMap_ofNat_ne_zero 2 h2) (algebraMap_ofNat_ne_zero 3 h3)
  rw [show (W⁄W.Ψ₃.SplittingField).Ψ₃ = W.Ψ₃.map (algebraMap F W.Ψ₃.SplittingField) from
    WeierstrassCurve.map_Ψ₃ ..] at hnodup
  simpa [Polynomial.aroots] using hnodup

section SplittingFieldΨ₃

variable (W) (L₁ : Type*) [Field L₁] [Algebra F L₁] [W.Ψ₃.IsSplittingField F L₁]

/-- **The `3`-division quartic of the base-changed curve splits** over a splitting field `L₁` of
`Ψ₃`.

This is Mathlib's `WeierstrassCurve.map_Ψ₃` — `(W⁄L₁).Ψ₃` is `W.Ψ₃` mapped along `F → L₁` — together
with the defining property of `L₁`.  It takes no hypothesis on the characteristic and does not need
`[W.IsElliptic]`. -/
theorem splits_Ψ₃_baseChange : (W⁄L₁).Ψ₃.Splits := by
  rw [show (W⁄L₁).Ψ₃ = W.Ψ₃.map (algebraMap F L₁) from WeierstrassCurve.map_Ψ₃ ..]
  exact IsSplittingField.splits L₁ W.Ψ₃

/-- **A splitting field of the `3`-division quartic is a Galois extension** of `F`, for an elliptic
curve over a field of characteristic `≠ 2, 3`.

`IsGalois.of_separable_splitting_field` at `separable_Ψ₃`, exactly as
`EllipticCurves.Torsion.TwoTorsionSplittingField`'s `isGalois_of_isSplittingField_Ψ₂Sq` is at
`separable_Ψ₂Sq`.  ⚠️ This is layer **one** of the tower only: `IsGalois F L₂` for the field this
file builds is false in general, because Galois is not transitive. -/
theorem isGalois_of_isSplittingField_Ψ₃ [W.IsElliptic] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    IsGalois F L₁ :=
  IsGalois.of_separable_splitting_field (p := W.Ψ₃) (separable_Ψ₃ h2 h3)

include W in
/-- **A splitting field of the `3`-division quartic is finite over `F`.**

Mathlib's `Polynomial.IsSplittingField.finiteDimensional`, whose only hypothesis is the
splitting-field instance: it takes no separability, no characteristic hypothesis and no
`[W.IsElliptic]`, which is why this and `isGalois_of_isSplittingField_Ψ₃` carry different
hypotheses. -/
theorem finiteDimensional_of_isSplittingField_Ψ₃ : FiniteDimensional F L₁ :=
  IsSplittingField.finiteDimensional L₁ W.Ψ₃

end SplittingFieldΨ₃

section YQuadratics

variable (W) (L₁ : Type*) [Field L₁] [Algebra F L₁]

open scoped Classical in
/-- **Layer two's polynomial**: the product of `X ^ 2 - C c` over the `Finset` of **values** `c`
that `(W⁄L₁).Ψ₂Sq` takes at the roots of `(W⁄L₁).Ψ₃`.  A splitting field of it over `L₁` is a field
over which `Ψ₂Sq` is a square at every root of `Ψ₃`, which is the second hypothesis of
`card_torsion_three_of_splits`.

⚠️ **Indexed by the VALUES, not by the roots, and the difference is separability.**  The product
over the roots repeats a factor whenever `Ψ₂Sq` takes one value at two of them, and a polynomial
with a repeated factor is not separable — so `separable_Ψ₂SqRootPoly` below, and with it
`isGalois_tower_top` and `isSeparable_tower`, would be unavailable.  Over the image `Finset` the
factors are distinct and pairwise coprime and the same splitting field is obtained, since the two
products have the same roots. -/
noncomputable def Ψ₂SqRootPoly : L₁[X] :=
  ∏ c ∈ (W⁄L₁).Ψ₃.roots.toFinset.image (fun x => (W⁄L₁).Ψ₂Sq.eval x), (X ^ 2 - C c)

variable {W L₁}

/-- **Layer two's polynomial is nonzero**: each factor `X ^ 2 - C c` is, whatever `c` is. -/
lemma Ψ₂SqRootPoly_ne_zero : Ψ₂SqRootPoly W L₁ ≠ 0 := by
  classical
  rw [Ψ₂SqRootPoly]
  refine Finset.prod_ne_zero_iff.mpr fun c _ => ?_
  exact X_pow_sub_C_ne_zero (by norm_num) c

/-- **At a root of `Ψ₃`, the quadratic cutting out the `y`-coordinates divides layer two's
polynomial** — which is how a square root of `Ψ₂Sq.eval x` is extracted from the splitting field.
⚠️ The hypothesis is that `x` is a root of `Ψ₃`, not that `Ψ₂Sq.eval x` is in any particular set:
the `Finset` is indexed by the values, and this is `Finset.mem_image_of_mem`. -/
lemma dvd_Ψ₂SqRootPoly {x : L₁} (hx : (W⁄L₁).Ψ₃.eval x = 0) (h3 : (3 : L₁) ≠ 0) :
    (X ^ 2 - C ((W⁄L₁).Ψ₂Sq.eval x)) ∣ Ψ₂SqRootPoly W L₁ := by
  classical
  refine Finset.dvd_prod_of_mem _ (Finset.mem_image_of_mem _ ?_)
  rw [Multiset.mem_toFinset, mem_roots ((W⁄L₁).Ψ₃_ne_zero h3)]
  exact hx

/-- **Layer two's polynomial is separable**, for an elliptic curve over a field of characteristic
`≠ 2, 3`.

Two halves, and both are paid by the indexing choice made at `Ψ₂SqRootPoly`.  Distinct factors are
coprime because their difference is the unit `C (d - c)`; and each factor is separable by
`Polynomial.separable_X_pow_sub_C`, whose `a ≠ 0` side condition is `Ψ₂Sq_eval_ne_zero_of_root_Ψ₃`
— the closure-free lemma `EllipticCurves.Torsion.ThreeTorsionStructure` states for exactly this
kind of consumer. -/
lemma separable_Ψ₂SqRootPoly [(W⁄L₁).IsElliptic] (h2 : (2 : L₁) ≠ 0) (h3 : (3 : L₁) ≠ 0) :
    (Ψ₂SqRootPoly W L₁).Separable := by
  classical
  rw [Ψ₂SqRootPoly]
  refine separable_prod' ?_ ?_
  · intro c hc d hd hcd
    have hne : d - c ≠ 0 := sub_ne_zero_of_ne (Ne.symm hcd)
    refine ⟨C (d - c)⁻¹, -C (d - c)⁻¹, ?_⟩
    have hrw : C (d - c)⁻¹ * (X ^ 2 - C c) + -C (d - c)⁻¹ * (X ^ 2 - C d)
        = C ((d - c)⁻¹ * (d - c)) := by rw [map_mul, map_sub]; ring
    rw [hrw, inv_mul_cancel₀ hne, map_one]
  · intro c hc
    simp only [Finset.mem_image, Multiset.mem_toFinset] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    rw [mem_roots ((W⁄L₁).Ψ₃_ne_zero h3)] at hx
    exact separable_X_pow_sub_C _ (by simpa using h2)
      (Ψ₂Sq_eval_ne_zero_of_root_Ψ₃ h2 hx)

end YQuadratics

section Tower

variable (W) (L₁ L₂ : Type*) [Field L₁] [Field L₂] [Algebra F L₁] [Algebra F L₂] [Algebra L₁ L₂]
  [IsScalarTower F L₁ L₂] [W.Ψ₃.IsSplittingField F L₁]
  [(Ψ₂SqRootPoly W L₁).IsSplittingField L₁ L₂]

variable {W L₂}

omit [W.Ψ₃.IsSplittingField F L₁] [(Ψ₂SqRootPoly W L₁).IsSplittingField L₁ L₂] in
/-- `Ψ₃` of the top of the tower is `Ψ₃` of the middle, mapped up: two applications of
`WeierstrassCurve.map_Ψ₃` and `IsScalarTower.algebraMap_eq`. -/
private lemma Ψ₃_eq_map : (W⁄L₂).Ψ₃ = ((W⁄L₁).Ψ₃).map (algebraMap L₁ L₂) := by
  rw [show (W⁄L₂).Ψ₃ = W.Ψ₃.map (algebraMap F L₂) from WeierstrassCurve.map_Ψ₃ ..,
    show (W⁄L₁).Ψ₃ = W.Ψ₃.map (algebraMap F L₁) from WeierstrassCurve.map_Ψ₃ ..,
    Polynomial.map_map, ← IsScalarTower.algebraMap_eq]

omit [W.Ψ₃.IsSplittingField F L₁] [(Ψ₂SqRootPoly W L₁).IsSplittingField L₁ L₂] in
/-- `Ψ₂Sq` of the top of the tower is `Ψ₂Sq` of the middle, mapped up. -/
private lemma Ψ₂Sq_eq_map : (W⁄L₂).Ψ₂Sq = ((W⁄L₁).Ψ₂Sq).map (algebraMap L₁ L₂) := by
  rw [show (W⁄L₂).Ψ₂Sq = W.Ψ₂Sq.map (algebraMap F L₂) from WeierstrassCurve.map_Ψ₂Sq ..,
    show (W⁄L₁).Ψ₂Sq = W.Ψ₂Sq.map (algebraMap F L₁) from WeierstrassCurve.map_Ψ₂Sq ..,
    Polynomial.map_map, ← IsScalarTower.algebraMap_eq]

omit [(Ψ₂SqRootPoly W L₁).IsSplittingField L₁ L₂] in
include L₁ in
/-- **The first condition, over the top of the tower**: `Ψ₃` splits over `L₂` because it already
splits over `L₁`.  `Polynomial.Splits.map`; no hypothesis on the characteristic and no
`[W.IsElliptic]`. -/
theorem splits_Ψ₃_tower : (W⁄L₂).Ψ₃.Splits := by
  rw [Ψ₃_eq_map L₁]
  exact (splits_Ψ₃_baseChange W L₁).map _

include L₁ in
/-- **The second condition, over the top of the tower**: `Ψ₂Sq` is a square at every root of `Ψ₃`
over `L₂`.

This is what layer two was built for, and it is three steps.  A root `z` of `(W⁄L₂).Ψ₃` is the image
of a root `x` of `(W⁄L₁).Ψ₃`, because `Ψ₃` splits over `L₁` and `Polynomial.Splits.roots_map`
identifies the two root multisets — ⚠️ this is the step that needs layer **one** to have been built
first, and it is why the two layers cannot be swapped.  Then `X ^ 2 - C ((W⁄L₁).Ψ₂Sq.eval x)`
divides `Ψ₂SqRootPoly`, which splits over `L₂`, so it splits over `L₂` and has a root `s` there.
Finally `(W⁄L₂).Ψ₂Sq.eval z` is the image of `(W⁄L₁).Ψ₂Sq.eval x`, which is `s ^ 2`. -/
theorem isSquare_Ψ₂Sq_eval_tower (h3 : (3 : F) ≠ 0) {z : L₂} (hz : (W⁄L₂).Ψ₃.eval z = 0) :
    IsSquare ((W⁄L₂).Ψ₂Sq.eval z) := by
  have h3₁ : (3 : L₁) ≠ 0 := algebraMap_ofNat_ne_zero 3 h3
  have h3₂ : (3 : L₂) ≠ 0 := algebraMap_ofNat_ne_zero 3 h3
  have hmem : z ∈ (W⁄L₂).Ψ₃.roots := (mem_roots ((W⁄L₂).Ψ₃_ne_zero h3₂)).mpr hz
  rw [Ψ₃_eq_map L₁, (splits_Ψ₃_baseChange W L₁).roots_map] at hmem
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hmem
  rw [mem_roots ((W⁄L₁).Ψ₃_ne_zero h3₁)] at hx
  set c : L₁ := (W⁄L₁).Ψ₂Sq.eval x with hc
  have hdvd : (X ^ 2 - C c) ∣ Ψ₂SqRootPoly W L₁ := dvd_Ψ₂SqRootPoly hx h3₁
  have hsplits : (((X : L₁[X]) ^ 2 - C c).map (algebraMap L₁ L₂)).Splits :=
    ((IsSplittingField.splits L₂ (Ψ₂SqRootPoly W L₁)).of_dvd
      (Polynomial.map_ne_zero Ψ₂SqRootPoly_ne_zero) (Polynomial.map_dvd _ hdvd))
  obtain ⟨s, hs⟩ := hsplits.exists_eval_eq_zero (by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    rw [degree_X_pow_sub_C (by norm_num)]
    exact by decide)
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, eval_sub,
    eval_pow, eval_X, eval_C, sub_eq_zero] at hs
  rw [Ψ₂Sq_eq_map L₁, eval_map, eval₂_hom, ← hc, ← hs]
  exact ⟨s, (sq s).symm ▸ rfl⟩

include L₁ in
/-- **`#E[3] = 9` over the top of the tower**, for an elliptic curve over a field of characteristic
`≠ 2, 3`.

`card_torsion_three_of_splits` over `L₂`, with both of its hypotheses discharged by the two
statements above rather than by an algebraic closure. -/
theorem card_torsion_three_tower [W.IsElliptic] [DecidableEq L₂] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) : Nat.card ((W⁄L₂).torsion 3) = 9 := by
  haveI : (W⁄L₂).IsElliptic := inferInstanceAs (W.map (algebraMap F L₂)).IsElliptic
  exact card_torsion_three_of_splits (algebraMap_ofNat_ne_zero 2 h2)
    (algebraMap_ofNat_ne_zero 3 h3) (splits_Ψ₃_tower L₁)
    fun _ hz => isSquare_Ψ₂Sq_eval_tower L₁ h3 hz

include L₁ in
/-- **`E[3] ≃+ ZMod 3 × ZMod 3` over the top of the tower**, for an elliptic curve over a field of
characteristic `≠ 2, 3`.  The structure theorem `nonempty_torsionThree_addEquiv_of_splits` at the
same two discharged hypotheses. -/
theorem nonempty_torsionThree_addEquiv_tower [W.IsElliptic] [DecidableEq L₂] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) : Nonempty ((W⁄L₂).torsion 3 ≃+ ZMod 3 × ZMod 3) := by
  haveI : (W⁄L₂).IsElliptic := inferInstanceAs (W.map (algebraMap F L₂)).IsElliptic
  exact nonempty_torsionThree_addEquiv_of_splits (algebraMap_ofNat_ne_zero 2 h2)
    (algebraMap_ofNat_ne_zero 3 h3) (splits_Ψ₃_tower L₁)
    fun _ hz => isSquare_Ψ₂Sq_eval_tower L₁ h3 hz

include L₁ W in
/-- **The tower is finite over `F`.**  Both layers are splitting fields, so both are finite, and
`FiniteDimensional.trans` composes them.  It takes no hypothesis on the characteristic and does not
need `[W.IsElliptic]`: finiteness of a splitting field is not about the discriminant. -/
theorem finiteDimensional_tower : FiniteDimensional F L₂ := by
  haveI : FiniteDimensional F L₁ := finiteDimensional_of_isSplittingField_Ψ₃ W L₁
  haveI : FiniteDimensional L₁ L₂ := IsSplittingField.finiteDimensional L₂ (Ψ₂SqRootPoly W L₁)
  exact FiniteDimensional.trans F L₁ L₂

omit [Algebra F L₂] [IsScalarTower F L₁ L₂] [W.Ψ₃.IsSplittingField F L₁] in
include L₁ in
/-- **Layer two is a Galois extension of layer one**, for an elliptic curve over a field of
characteristic `≠ 2, 3`: `IsGalois.of_separable_splitting_field` at `separable_Ψ₂SqRootPoly`.
⚠️ This is `L₂ / L₁` and says nothing about `L₂ / F`. -/
theorem isGalois_tower_top [W.IsElliptic] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    IsGalois L₁ L₂ := by
  haveI : (W⁄L₁).IsElliptic := inferInstanceAs (W.map (algebraMap F L₁)).IsElliptic
  exact IsGalois.of_separable_splitting_field (p := Ψ₂SqRootPoly W L₁)
    (separable_Ψ₂SqRootPoly (algebraMap_ofNat_ne_zero 2 h2) (algebraMap_ofNat_ne_zero 3 h3))

include L₁ in
/-- **The tower is separable over `F`**, for an elliptic curve over a field of characteristic
`≠ 2, 3`: both layers are Galois, hence separable, and `Algebra.IsSeparable.trans` composes them.

⚠️ **The corresponding composition for `IsGalois` does not exist and the statement it would give is
false**: normality is not transitive.  This lemma and `finiteDimensional_tower` are together the
input under which the normal closure of `L₂ / F` is Galois, and forming that closure is deliberately
not done here. -/
theorem isSeparable_tower [W.IsElliptic] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Algebra.IsSeparable F L₂ := by
  haveI := isGalois_of_isSplittingField_Ψ₃ W L₁ h2 h3
  haveI := isGalois_tower_top (W := W) L₁ (L₂ := L₂) h2 h3
  exact Algebra.IsSeparable.trans F L₁ L₂

end Tower

/-! ## Both conditions are inherited by every extension

⚠️ **Neither condition is about the tower, and this section says so by proving them over an
arbitrary `F`-algebra map.**  `splits_Ψ₃_tower` and `isSquare_Ψ₂Sq_eval_tower` above are stated at
the top of the tower because that is where layer two *establishes* them; once established they go
up any `F`-algebra map for free, and the consumer that wants that is the Galois closure below,
which is **not** a scalar extension of `L₂` by any instance the tower supplies.

The first is `Polynomial.Splits.map` and nothing else.  The second is the same three-step argument
`isSquare_Ψ₂Sq_eval_tower` runs, with its middle step — *divide `Ψ₂SqRootPoly` and take a root* —
replaced by the hypothesis: a root `z` upstairs is `φ x` for a root `x` downstairs because `Ψ₃`
already splits downstairs, and `IsSquare` is carried by any ring hom. ⚠️ **The splitting hypothesis
is doing the work in both, and it cannot be dropped**: without it a new root can appear upstairs
and nothing downstairs says anything about `Ψ₂Sq` there. -/

section AlgHom

variable {L M : Type*} [Field L] [Field M] [Algebra F L] [Algebra F M]

/-- `Ψ₃` over `M` is `Ψ₃` over `L` pushed along an `F`-algebra map: `WeierstrassCurve.map_Ψ₃` at
both ends and `AlgHom.comp_algebraMap`.  The scalar-tower form is `Ψ₃_eq_map` above; this one takes
a map rather than an instance, which is what an `IntermediateField` needs. -/
private lemma Ψ₃_eq_map_algHom (φ : L →ₐ[F] M) : (W⁄M).Ψ₃ = ((W⁄L).Ψ₃).map φ := by
  rw [show (W⁄M).Ψ₃ = W.Ψ₃.map (algebraMap F M) from WeierstrassCurve.map_Ψ₃ ..,
    show (W⁄L).Ψ₃ = W.Ψ₃.map (algebraMap F L) from WeierstrassCurve.map_Ψ₃ ..,
    Polynomial.map_map, ← φ.comp_algebraMap]

/-- `Ψ₂Sq` over `M` is `Ψ₂Sq` over `L` pushed along an `F`-algebra map. -/
private lemma Ψ₂Sq_eq_map_algHom (φ : L →ₐ[F] M) : (W⁄M).Ψ₂Sq = ((W⁄L).Ψ₂Sq).map φ := by
  rw [show (W⁄M).Ψ₂Sq = W.Ψ₂Sq.map (algebraMap F M) from WeierstrassCurve.map_Ψ₂Sq ..,
    show (W⁄L).Ψ₂Sq = W.Ψ₂Sq.map (algebraMap F L) from WeierstrassCurve.map_Ψ₂Sq ..,
    Polynomial.map_map, ← φ.comp_algebraMap]

/-- **The first condition goes up any `F`-algebra map.**  It takes no hypothesis on the
characteristic and no `[W.IsElliptic]`: `Polynomial.Splits.map` is the whole proof. -/
theorem splits_Ψ₃_of_algHom (φ : L →ₐ[F] M) (h : (W⁄L).Ψ₃.Splits) : (W⁄M).Ψ₃.Splits := by
  rw [Ψ₃_eq_map_algHom φ]
  exact h.map _

/-- **The second condition goes up any `F`-algebra map, given the first downstairs.**

⚠️ **`hsplits` is a hypothesis of this statement and not a consequence of `hsq`.**  It is what
identifies the roots of `(W⁄M).Ψ₃` with the images of the roots of `(W⁄L).Ψ₃`
(`Polynomial.Splits.roots_map`); over an `M` where `Ψ₃` gains a root, `hsq` downstairs says nothing
at all about that root.  Given it, the argument is two rewrites: `z = φ x` for a root `x` of
`(W⁄L).Ψ₃`, and `(W⁄M).Ψ₂Sq.eval (φ x) = φ ((W⁄L).Ψ₂Sq.eval x)`, which is `φ s * φ s`. -/
theorem isSquare_Ψ₂Sq_eval_of_algHom (h3 : (3 : F) ≠ 0) (φ : L →ₐ[F] M)
    (hsplits : (W⁄L).Ψ₃.Splits)
    (hsq : ∀ x : L, (W⁄L).Ψ₃.eval x = 0 → IsSquare ((W⁄L).Ψ₂Sq.eval x))
    {z : M} (hz : (W⁄M).Ψ₃.eval z = 0) : IsSquare ((W⁄M).Ψ₂Sq.eval z) := by
  have h3L : (3 : L) ≠ 0 := algebraMap_ofNat_ne_zero 3 h3
  have h3M : (3 : M) ≠ 0 := algebraMap_ofNat_ne_zero 3 h3
  have hmem : z ∈ (W⁄M).Ψ₃.roots := (mem_roots ((W⁄M).Ψ₃_ne_zero h3M)).mpr hz
  rw [Ψ₃_eq_map_algHom φ, hsplits.roots_map] at hmem
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hmem
  rw [mem_roots ((W⁄L).Ψ₃_ne_zero h3L)] at hx
  obtain ⟨s, hs⟩ := hsq x hx
  rw [Ψ₂Sq_eq_map_algHom φ, eval_map, eval₂_hom, hs, map_mul]
  exact ⟨φ s, rfl⟩

/-- **`#E[3] = 9` goes up any `F`-algebra map out of a field where both conditions hold**, for an
elliptic curve over a field of characteristic `≠ 2, 3`.  `card_torsion_three_of_splits` over `M`,
with its two hypotheses supplied by the two statements above. -/
theorem card_torsion_three_of_algHom [W.IsElliptic] [DecidableEq M] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (φ : L →ₐ[F] M) (hsplits : (W⁄L).Ψ₃.Splits)
    (hsq : ∀ x : L, (W⁄L).Ψ₃.eval x = 0 → IsSquare ((W⁄L).Ψ₂Sq.eval x)) :
    Nat.card ((W⁄M).torsion 3) = 9 := by
  haveI : (W⁄M).IsElliptic := inferInstanceAs (W.map (algebraMap F M)).IsElliptic
  exact card_torsion_three_of_splits (algebraMap_ofNat_ne_zero 2 h2)
    (algebraMap_ofNat_ne_zero 3 h3) (splits_Ψ₃_of_algHom φ hsplits)
    fun _ hz => isSquare_Ψ₂Sq_eval_of_algHom h3 φ hsplits hsq hz

/-- **`E[3] ≃+ ZMod 3 × ZMod 3` goes up any `F`-algebra map out of a field where both conditions
hold**, for an elliptic curve over a field of characteristic `≠ 2, 3`. -/
theorem nonempty_torsionThree_addEquiv_of_algHom [W.IsElliptic] [DecidableEq M] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (φ : L →ₐ[F] M) (hsplits : (W⁄L).Ψ₃.Splits)
    (hsq : ∀ x : L, (W⁄L).Ψ₃.eval x = 0 → IsSquare ((W⁄L).Ψ₂Sq.eval x)) :
    Nonempty ((W⁄M).torsion 3 ≃+ ZMod 3 × ZMod 3) := by
  haveI : (W⁄M).IsElliptic := inferInstanceAs (W.map (algebraMap F M)).IsElliptic
  exact nonempty_torsionThree_addEquiv_of_splits (algebraMap_ofNat_ne_zero 2 h2)
    (algebraMap_ofNat_ne_zero 3 h3) (splits_Ψ₃_of_algHom φ hsplits)
    fun _ hz => isSquare_Ψ₂Sq_eval_of_algHom h3 φ hsplits hsq hz

end AlgHom

section Concrete

variable (W)

/-- **The `3`-division field** of `W`: the tower built at the canonical splitting fields, a
splitting field of `Ψ₂SqRootPoly` over a splitting field of `Ψ₃`.

⚠️ It is an `abbrev` on purpose.  Mathlib already supplies `Algebra F` and `IsScalarTower F L₁` for
an iterated `SplittingField`, and a reducible definition inherits all of them; declaring either by
hand — as `((algebraMap _ _).comp (algebraMap F _)).toAlgebra` — produces a diamond against
Mathlib's own instance that does not typecheck. -/
noncomputable abbrev threeDivisionField : Type _ :=
  (Ψ₂SqRootPoly W W.Ψ₃.SplittingField).SplittingField

/-- **`#E[3] = 9` over the `3`-division field**, for an elliptic curve over a field of
characteristic `≠ 2, 3` — with no splitting-field instance for the caller to supply. -/
theorem card_torsion_three_threeDivisionField [W.IsElliptic] [DecidableEq (threeDivisionField W)]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nat.card ((W⁄(threeDivisionField W)).torsion 3) = 9 :=
  card_torsion_three_tower (W := W) W.Ψ₃.SplittingField h2 h3

/-- **`E[3] ≃+ ZMod 3 × ZMod 3` over the `3`-division field**, for an elliptic curve over a field of
characteristic `≠ 2, 3`. -/
theorem nonempty_torsionThree_addEquiv_threeDivisionField [W.IsElliptic]
    [DecidableEq (threeDivisionField W)] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nonempty ((W⁄(threeDivisionField W)).torsion 3 ≃+ ZMod 3 × ZMod 3) :=
  nonempty_torsionThree_addEquiv_tower (W := W) W.Ψ₃.SplittingField h2 h3

/-- **The `3`-division field is finite over `F`.** -/
theorem finiteDimensional_threeDivisionField : FiniteDimensional F (threeDivisionField W) :=
  finiteDimensional_tower (W := W) W.Ψ₃.SplittingField

/-- **The `3`-division field is separable over `F`**, for an elliptic curve over a field of
characteristic `≠ 2, 3`. -/
theorem isSeparable_threeDivisionField [W.IsElliptic] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Algebra.IsSeparable F (threeDivisionField W) :=
  isSeparable_tower (W := W) W.Ψ₃.SplittingField h2 h3

end Concrete

/-! ## The Galois closure

`isSeparable_threeDivisionField` and `finiteDimensional_threeDivisionField` are together exactly
the hypotheses under which the normal closure of the `3`-division field over `F` is Galois, and
this section forms it.  The Galois half is `EllipticCurves.Galois.NormalClosureSeparable`'s
`isGalois_normalClosure_of_isSeparable`, **cited and not repeated**: it is curve-free, it takes no
finiteness, and its own file records why `IsGalois.normalClosure` does not prove it at the pin.

⚠️ **What the closure fails is the tower's own `[Algebra L₁ L₂]` and not only the splitting-field
instance**, and the difference decides which statements above can reach it.  Mathlib does give
`Algebra L₂ ↥(normalClosure ‥)` and `IsScalarTower F L₂ ↥(normalClosure ‥)` for a normal closure,
and `IsScalarTower.toAlgHom` is how the map below is built — so a map **out of** `L₂` is available.
An `IntermediateField F (AlgebraicClosure L₂)`, taken as its own `L₂`, satisfies **neither**
`[Algebra L₁ L₂]`, which all **seven** `_tower` statements bind, **nor**
`[(Ψ₂SqRootPoly W L₁).IsSplittingField L₁ L₂]`, which **six** of them bind — ⚠️ `splits_Ψ₃_tower`
`omit`s that one.  ⚠️ **Both counts are read off the elaborated types and not off the source**:
`#check @splits_Ψ₃_tower` against `#check @isSquare_Ψ₂Sq_eval_tower` settles the pair in one
command.  ⚠️ **At the closure `splits_Ψ₃_tower` fails on TWO of them, and those two are the whole
list**: it fails on `Algebra (Ψ₃ W).SplittingField (threeDivisionGaloisField W)`, then — with that
one supplied by hand — on `IsScalarTower F (Ψ₃ W).SplittingField (threeDivisionGaloisField W)`,
and with both supplied the same term elaborates.  That second instance **six** of the seven bind
as well, all but `isGalois_tower_top`, which `omit`s it together with `[Algebra F L₂]` — so the
tower's three relative instances read **7 / 6 / 6**, and the two sixes exclude **different**
statements.  That is why the two conditions are transported along an `AlgHom` in the section
above, and the `AlgHom` statements are the general ones and cost nothing extra.

⚠️ **Galois over `F` is strictly more than either floor gives.**  `isGalois_of_isSplittingField_Ψ₃`
is `L₁ / F` and `isGalois_tower_top` is `L₂ / L₁`; normality is not transitive, so neither composes
into `L₂ / F` and the statement that would say so is false in general. -/

section GaloisClosure

variable (W)

/-- **The Galois closure of the `3`-division field**: the normal closure of `threeDivisionField W`
over `F`, taken inside an algebraic closure of it.

⚠️ It is an `abbrev` for the same reason `threeDivisionField` is: Mathlib supplies
`Algebra (threeDivisionField W) ↥(normalClosure ‥)` and `IsScalarTower F (threeDivisionField W) ‥`
for a normal closure, and a reducible definition inherits them. -/
noncomputable abbrev threeDivisionGaloisField : Type _ :=
  IntermediateField.normalClosure F (threeDivisionField W)
    (AlgebraicClosure (threeDivisionField W))

/-- **The Galois closure is Galois over `F`**, for an elliptic curve over a field of characteristic
`≠ 2, 3`: `isSeparable_threeDivisionField` fed to `EllipticCurves.Galois.NormalClosureSeparable`'s
curve-free `isGalois_normalClosure_of_isSeparable`.  ⚠️ This is the statement `isSeparable_tower`
was built for and the one neither floor of the tower gives. -/
theorem isGalois_threeDivisionGaloisField [W.IsElliptic] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    IsGalois F (threeDivisionGaloisField W) := by
  haveI := isSeparable_threeDivisionField W h2 h3
  exact _root_.isGalois_normalClosure_of_isSeparable F (threeDivisionField W)

/-- **The Galois closure is finite over `F`.**  `normalClosure.is_finiteDimensional` at
`finiteDimensional_threeDivisionField`; it takes no hypothesis on the characteristic and does not
need `[W.IsElliptic]`. -/
theorem finiteDimensional_threeDivisionGaloisField :
    FiniteDimensional F (threeDivisionGaloisField W) := by
  haveI := finiteDimensional_threeDivisionField W
  infer_instance

/-- **`#E[3] = 9` over the Galois closure**, for an elliptic curve over a field of characteristic
`≠ 2, 3`.  `card_torsion_three_of_algHom` along `IsScalarTower.toAlgHom`, at the two conditions the
tower already establishes over `threeDivisionField W`. -/
theorem card_torsion_three_threeDivisionGaloisField [W.IsElliptic]
    [DecidableEq (threeDivisionGaloisField W)] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nat.card ((W⁄(threeDivisionGaloisField W)).torsion 3) = 9 :=
  card_torsion_three_of_algHom h2 h3
    (IsScalarTower.toAlgHom F (threeDivisionField W) (threeDivisionGaloisField W))
    (splits_Ψ₃_tower (W := W) W.Ψ₃.SplittingField)
    fun _ hz => isSquare_Ψ₂Sq_eval_tower (W := W) W.Ψ₃.SplittingField h3 hz

/-- **`E[3] ≃+ ZMod 3 × ZMod 3` over the Galois closure**, for an elliptic curve over a field of
characteristic `≠ 2, 3`. -/
theorem nonempty_torsionThree_addEquiv_threeDivisionGaloisField [W.IsElliptic]
    [DecidableEq (threeDivisionGaloisField W)] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nonempty ((W⁄(threeDivisionGaloisField W)).torsion 3 ≃+ ZMod 3 × ZMod 3) :=
  nonempty_torsionThree_addEquiv_of_algHom h2 h3
    (IsScalarTower.toAlgHom F (threeDivisionField W) (threeDivisionGaloisField W))
    (splits_Ψ₃_tower (W := W) W.Ψ₃.SplittingField)
    fun _ hz => isSquare_Ψ₂Sq_eval_tower (W := W) W.Ψ₃.SplittingField h3 hz

end GaloisClosure

section Nonvacuity

open EllipticCurves.Fixture

private lemma Ψ₃_y2AddYEqX3 :
    (y2AddYEqX3 ℚ).Ψ₃ = C 3 * X * ((X + 1) * (X ^ 2 - X + 1)) := by
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, y2AddYEqX3]
  norm_num only
  simp only [map_ofNat, Polynomial.C_0, Polynomial.C_1]
  ring

private lemma eval_Ψ₃_y2AddYEqX3_eq_zero_iff {x : ℚ} :
    (y2AddYEqX3 ℚ).Ψ₃.eval x = 0 ↔ x = 0 ∨ x = -1 := by
  rw [Ψ₃_y2AddYEqX3]
  simp only [eval_mul, eval_add, eval_sub, eval_pow, eval_C, eval_X, eval_one]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | hx
      · norm_num at h''
      · exact Or.inl hx
    · rcases mul_eq_zero.mp h' with hx | hq
      · exact Or.inr (by linarith)
      · nlinarith [sq_nonneg (2 * x - 1)]
  · rintro (rfl | rfl) <;> ring

private lemma card_roots_Ψ₃_y2AddYEqX3 :
    Nat.card {x : ℚ // (y2AddYEqX3 ℚ).Ψ₃.eval x = 0} = 2 := by
  have e : {x : ℚ // (y2AddYEqX3 ℚ).Ψ₃.eval x = 0} ≃ (({0, -1} : Set ℚ) : Type) :=
    Equiv.subtypeEquivRight fun x => by
      rw [eval_Ψ₃_y2AddYEqX3_eq_zero_iff]
      simp
  rw [Nat.card_congr e, Nat.card_coe_set_eq, Set.ncard_pair (by norm_num)]

private theorem not_splits_Ψ₃_y2AddYEqX3 : ¬ (y2AddYEqX3 ℚ).Ψ₃.Splits := by
  intro h
  have h4 := card_roots_Ψ₃_of_splits (W := y2AddYEqX3 ℚ) (by norm_num) (by norm_num) h
  rw [card_roots_Ψ₃_y2AddYEqX3] at h4
  omega

private noncomputable instance : DecidableEq (threeDivisionField (y2AddYEqX3 ℚ)) :=
  Classical.decEq _

private theorem card_torsion_three_threeDivisionField_y2AddYEqX3 :
    Nat.card (((y2AddYEqX3 ℚ)⁄(threeDivisionField (y2AddYEqX3 ℚ))).torsion 3) = 9 :=
  card_torsion_three_threeDivisionField _ (by norm_num) (by norm_num)

private noncomputable instance : DecidableEq (threeDivisionGaloisField (y2AddYEqX3 ℚ)) :=
  Classical.decEq _

private theorem isGalois_threeDivisionGaloisField_y2AddYEqX3 :
    IsGalois ℚ (threeDivisionGaloisField (y2AddYEqX3 ℚ)) :=
  isGalois_threeDivisionGaloisField _ (by norm_num) (by norm_num)

private theorem card_torsion_three_threeDivisionGaloisField_y2AddYEqX3 :
    Nat.card (((y2AddYEqX3 ℚ)⁄(threeDivisionGaloisField (y2AddYEqX3 ℚ))).torsion 3) = 9 :=
  card_torsion_three_threeDivisionGaloisField _ (by norm_num) (by norm_num)

end Nonvacuity

end WeierstrassCurve.Affine
