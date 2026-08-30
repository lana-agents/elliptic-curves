/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByNPullback
import EllipticCurves.FunctionField.MulByThreeDegree
import EllipticCurves.FunctionField.NegYGalois
import EllipticCurves.FunctionField.TranslationDoublingCommGeneral

/-!
# `x(n • 𝒫)` is a rational function of `x`, for every `n`

`EllipticCurves.FunctionField.MulByNPullback` builds the group multiple `n • 𝒫` of the generic
point for every `n`, out of the group law and with no division polynomial.  This file proves that
its `x`-coordinate lies in the **rational function subfield** `F(x) = ratFuncRange W`, and names the
rational function it is:

```
(n • 𝒫).xCoord ∈ ratFuncRange W        and        algebraMap (RatFunc F) F(W) (nMulRatFunc W n)
                                                    = (n • 𝒫).xCoord.
```

The reason is the group law and nothing else: the hyperelliptic involution `ι = negYAlgEquiv W`
sends `𝒫` to `-𝒫`, hence — being additive on points — sends `n • 𝒫` to `-(n • 𝒫)`, whose
`x`-coordinate is the same one.  So `x(n • 𝒫)` is `ι`-fixed, and `F(x)` is the fixed field of `ι`.

## ⚠️ The fixed field is **already merged**, and this file consumes it

`#1180` was filed saying that *"there is no statement of the form `F⟮genX W⟯` is the fixed field of
`ι`, in any packaging"*, having checked `EllipticCurves.FunctionField.NegYInvolution`.  That is
true of *that* file and false of the tree: `EllipticCurves.FunctionField.NegYGalois` proves

```
ratFuncRange_eq_fixedField_negYGroup :  ratFuncRange W = IntermediateField.fixedField (negYGroup W)
```

with `negYGroup W = Subgroup.zpowers (negYAlgEquiv W)`, and proves `orderOf_negYAlgEquiv = 2`,
`card_negYGroup = 2`, `finrank_fixedField_negYGroup = 2` and `ratFuncRange_le_fixedField_negYGroup`
besides — the whole Artin sandwich, over an arbitrary field and in every characteristic, together
with the Galois package `isGalois_ratFuncRange` / `isGalois_ratFunc` on top of it.

**Nothing of that is re-proved here.**  What this file adds is the step `#1180` identified as the
one where the group law enters — `x(n • 𝒫)` is `ι`-fixed — together with the `RatFunc F`
presentation a degree computation consumes.

## Main definitions and statements

⚠️ Every public declaration of this file is listed.  Two of them are `def`s, which is why the
heading is not `## Main results`.

* `IntermediateField.mem_fixedField_zpowers_iff` — for a single automorphism, membership of the
  fixed field of the subgroup it generates is just being fixed by it; the general form of the
  stabilizer argument `NegYGalois`'s `genX_mem_fixedField_negYGroup` runs inline;
* `WeierstrassCurve.Affine.Point.xCoord_neg` — `x(-P) = x(P)`, junk values included;
* `WeierstrassCurve.Affine.CoordinateRing.mem_ratFuncRange_iff_negYAlgEquiv_eq` — the merged fixed
  field in the pointwise form a caller uses: `z ∈ F(x) ↔ ι z = z` — with the one-directional
  `…mem_ratFuncRange_of_negYAlgEquiv_eq`, which is the direction this file consumes;
* `WeierstrassCurve.Affine.CoordinateRing.xCoord_genPointHom` — the `x`-coordinate transports along
  the point action of an `F`-algebra endomorphism;
* `WeierstrassCurve.Affine.CoordinateRing.genPointHom_negYAlgEquiv_genericPoint` — `ι` acts on
  `(W ⁄ F(W)).Point` as negation of the generic point;
* `WeierstrassCurve.Affine.CoordinateRing.negYAlgEquiv_xCoord_nsmul_genericPoint` — `ι` fixes
  `x(n • 𝒫)`.  ⚠️ This is the step where the group law enters and the only one that is not
  transport;
* `WeierstrassCurve.Affine.CoordinateRing.xCoord_nsmul_genericPoint_mem_ratFuncRange` — the
  headline: `(n • 𝒫).xCoord ∈ F(x)` for every `n : ℕ`, with no hypothesis on `n` and none on `F`;
* `WeierstrassCurve.Affine.CoordinateRing.ratFuncPreimage` with `algebraMap_ratFuncPreimage` — the
  name in `RatFunc F` of an element of `F(x)`, through the merged `ratFuncEquivRatFuncRange`;
* `WeierstrassCurve.Affine.CoordinateRing.nMulRatFunc` with `algebraMap_nMulRatFunc` — the same
  element named in `RatFunc F`, and `nMulRatFunc_two` / `nMulRatFunc_three` identifying it at
  `n = 2` and `n = 3` with the merged `doublingRatFunc` and `triplingRatFunc`.

## ⚠️ What this does **not** give

* **No degree, and in particular not `[F(W) : [n]∗F(W)] = n²`.**  `#1169`'s measurement
  (`EllipticCurves.FunctionField.MulByNPlacePullback`) records that rung 3 of `#639` needs, on top
  of `x ∘ [n] ∈ F(x)` — which is what this file supplies — the *reduced* numerator and denominator
  of the fraction, which is what `RatFunc.finrank_eq_max_natDegree` reads the degree off.  Nothing
  here says what those are: `nMulRatFunc` is produced by an inverse isomorphism, not by writing
  down a fraction, so it has no numerator and no denominator to read.  ⚠️ **Being an element of
  `F(x)` is not being a written-down rational function**, and it is the second that a degree count
  consumes.

  ⚠️ What remains is therefore `nMulRatFunc W n = Φₙ/ΨSqₙ` (`#404` / `#251`), the coprimality
  `IsCoprime (W.Φ n) (W.ΨSq n)` at general `n` (`#1184`; `#681` is the merged `n = 2` instance and
  is *not* the general gate), and `natDegree_ΨSq`'s `(n : F) ≠ 0`.  ⚠️ The degrees themselves are
  **not** gated — `natDegree_Φ` and `natDegree_ΨSq` are Mathlib's at general `n`.

  ⚠️ **A reader who takes this file for "rung 3 generalises at general `n`" has misread it.**  What
  it does is remove one of rung 3's gates.

  ⚠️ **What `nMulRatFunc` *is* enough for is the whole tower.**
  `EllipticCurves.FunctionField.MulByNDegreeTower` — which imports this file — proves
  `[F(W) : [n]∗F(W)] = [F(x) : F(nMulRatFunc W n)]` for every `n`, out of `algebraMap_nMulRatFunc`
  and nothing else about `n`.  So the element this file names is the tower's entire input; what is
  still missing is the **degree** of that element, which is the three gates listed just above.  That
  file proves no degree at any `n` outside `{2, 3}` either.

  ⚠️ **The tree does know degrees outside `{2, 3}`, by a different route.**
  `EllipticCurves.FunctionField.MulByNComposition` proves `[m · n]∗ = [m]∗ ∘ [n]∗` from the group
  law, so the two merged degrees multiply up to `[F(W) : [n]∗F(W)] = n²` at every `3`-smooth `n` —
  with no fraction, no coprimality and no `(n : F) ≠ 0`.  The three gates above are what stands
  between `3`-smooth and general `n`; they are not what stands between `{2, 3}` and everything else.
* **Nothing about rung 4.**  `ordInfty ([n]∗ genX) = -2` is *false* at general `n`
  (`MulByNPlacePullback`), and nothing here changes that.
* **It does not close `#404`.**  The coordinates of `[n]` as an explicit fraction remain
  unavailable; `nMulRatFunc W n` is a rational function whose existence is proved, not one that is
  written down.
* **No `[IsAlgClosed F]`, no `(2 : F) ≠ 0`, no hypothesis on `n`.**  At an `n` with `n • 𝒫 = 0`
  both sides are the junk value `0` and the statement is still true, so no non-degeneracy
  hypothesis is needed and none is added.  The non-vacuity certificate is over `ℚ` for the same
  reason.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2 and III.2.
-/

namespace IntermediateField

/-- **Membership of the fixed field of a single automorphism.**  `Subgroup.zpowers σ` is generated
by `σ`, and the elements of `L` that `σ` fixes are the stabilizer of `z`, which is a subgroup — so
being fixed by every power of `σ` is no more than being fixed by `σ` itself.

⚠️ `EllipticCurves.FunctionField.NegYGalois`'s `genX_mem_fixedField_negYGroup` runs this argument
inline at one element; this is the same argument with the element and the automorphism abstracted,
and it is what makes `mem_ratFuncRange_iff_negYAlgEquiv_eq` below a rewrite. -/
theorem mem_fixedField_zpowers_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    {σ : L ≃ₐ[K] L} {z : L} : z ∈ fixedField (Subgroup.zpowers σ) ↔ σ z = z := by
  rw [mem_fixedField_iff]
  refine ⟨fun h => h σ (Subgroup.mem_zpowers σ), fun h f hf => ?_⟩
  exact (Subgroup.zpowers_le (H := MulAction.stabilizer (L ≃ₐ[K] L) z)).mpr h hf

end IntermediateField

namespace WeierstrassCurve.Affine

namespace Point

/-- **Negation does not move the `x`-coordinate.**  Both sides are the junk value `0` at the point
at infinity, so no non-degeneracy hypothesis appears. -/
@[simp] theorem xCoord_neg {R : Type*} [CommRing R] {W' : Affine R} (P : W'.Point) :
    (-P).xCoord = P.xCoord := by
  cases P with
  | zero => change (-(0 : W'.Point)).xCoord = (0 : W'.Point).xCoord; rw [neg_zero]
  | some x y h => rw [neg_some, xCoord_some, xCoord_some]

end Point

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

/-! ### The merged fixed field, in pointwise form -/

/-- **`z ∈ F(x)` exactly when the hyperelliptic involution fixes `z`.**

This is the merged `ratFuncRange_eq_fixedField_negYGroup`
(`EllipticCurves.FunctionField.NegYGalois`) read through
`IntermediateField.mem_fixedField_zpowers_iff`; the mathematics — Artin's theorem against
`finrank_ratFuncRange = 2`, in every characteristic — is entirely there and none of it is repeated
here. -/
theorem mem_ratFuncRange_iff_negYAlgEquiv_eq [W.IsElliptic] {z : W.FunctionField} :
    z ∈ ratFuncRange W ↔ negYAlgEquiv W z = z := by
  rw [ratFuncRange_eq_fixedField_negYGroup, negYGroup]
  exact IntermediateField.mem_fixedField_zpowers_iff

/-- The direction this file uses: an `ι`-fixed element of `F(W)` is a rational function of `x`. -/
theorem mem_ratFuncRange_of_negYAlgEquiv_eq [W.IsElliptic] {z : W.FunctionField}
    (hz : negYAlgEquiv W z = z) : z ∈ ratFuncRange W :=
  mem_ratFuncRange_iff_negYAlgEquiv_eq.mpr hz

/-! ### The involution on points -/

/-- The `x`-coordinate transports along the point action of an `F`-algebra endomorphism.  At the
point at infinity both sides are `0`, `φ` being a ring homomorphism. -/
theorem xCoord_genPointHom (φ : W.FunctionField →ₐ[F] W.FunctionField)
    (P : (W.map (algebraMap F W.FunctionField)).Point) :
    (genPointHom φ P).xCoord = φ P.xCoord := by
  cases P with
  | zero =>
      change (genPointHom φ 0).xCoord
        = φ (0 : (W.map (algebraMap F W.FunctionField)).Point).xCoord
      rw [map_zero, Point.xCoord_zero, map_zero]
  | some x y h => rw [genPointHom_some, Point.xCoord_some, Point.xCoord_some]

variable (W) in
/-- **`ι` acts on `(W ⁄ F(W)).Point` as negation of the generic point.**  It fixes `genX` and sends
`genY` to `negY (genX, genY)` (`negYAlgEquiv_genY'`), which are exactly the coordinates of `-𝒫`.

`EllipticCurves.FunctionField.NegYInvolution` records the coordinate half of this as *"`ι` is the
negation of the generic point"*; this is that sentence as an equation in the group. -/
theorem genPointHom_negYAlgEquiv_genericPoint [W.IsElliptic] :
    genPointHom (negYAlgEquiv W : W.FunctionField →ₐ[F] W.FunctionField) genericPoint
      = -genericPoint (W := W) := by
  rw [genericPoint, genPointHom_some, Point.neg_some, Point.some.injEq]
  exact ⟨negYAlgEquiv_genX W, negYAlgEquiv_genY' W⟩

open Classical in
/-- **`ι` fixes `x(n • 𝒫)`, for every `n`.**  `genPointHom ι` is an `AddMonoidHom`, so it carries
`n • 𝒫` to `n • (-𝒫) = -(n • 𝒫)`, and negation does not move an `x`-coordinate.

⚠️ This is the step where the group law enters, and it is the only step of this file that is not
transport. -/
theorem negYAlgEquiv_xCoord_nsmul_genericPoint [W.IsElliptic] (n : ℕ) :
    negYAlgEquiv W (n • genericPoint (W := W)).xCoord
      = (n • genericPoint (W := W)).xCoord := by
  have h := xCoord_genPointHom (negYAlgEquiv W : W.FunctionField →ₐ[F] W.FunctionField)
    (n • genericPoint (W := W))
  rw [map_nsmul, genPointHom_negYAlgEquiv_genericPoint, neg_nsmul, Point.xCoord_neg] at h
  exact h.symm

open Classical in
/-- **`x(n • 𝒫) ∈ F(x)`, for every `n : ℕ`.**

`#1169`'s rung-3 measurement identified this as *true at general `n` for a reason the group law
supplies, but unavailable*, because the fixed field was not known to it.  The fixed field is merged
(`NegYGalois`), so this is now a two-step consequence.

⚠️ It is not a degree; see the module docstring for what rung 3 still needs. -/
theorem xCoord_nsmul_genericPoint_mem_ratFuncRange [W.IsElliptic] (n : ℕ) :
    (n • genericPoint (W := W)).xCoord ∈ ratFuncRange W :=
  mem_ratFuncRange_of_negYAlgEquiv_eq (negYAlgEquiv_xCoord_nsmul_genericPoint n)

/-! ### The `RatFunc F` presentation -/

variable (W) in
/-- The name in `RatFunc F` of an element of `F(x) ⊆ F(W)`, through the merged tautological
isomorphism `ratFuncEquivRatFuncRange : RatFunc F ≃+* F(x)`.  The map `RatFunc F → F(W)` is
injective, so the name is unique. -/
noncomputable def ratFuncPreimage {z : W.FunctionField} (hz : z ∈ ratFuncRange W) : RatFunc F :=
  (ratFuncEquivRatFuncRange W).symm ⟨z, hz⟩

@[simp] theorem algebraMap_ratFuncPreimage {z : W.FunctionField} (hz : z ∈ ratFuncRange W) :
    algebraMap (RatFunc F) W.FunctionField (ratFuncPreimage W hz) = z :=
  congrArg Subtype.val ((ratFuncEquivRatFuncRange W).apply_symm_apply ⟨z, hz⟩)

open Classical in
/-- **`x(n • 𝒫)` as a rational function of `x`.**  The general-`n` analogue of the merged
`doublingRatFunc`, reached from the group law instead of from `Φ₂/Ψ₂Sq`.

⚠️ **Its reduced numerator and denominator are not identified**, and that — not its existence — is
what a degree computation needs.  See the module docstring. -/
noncomputable def nMulRatFunc (W : Affine F) [W.IsElliptic] (n : ℕ) : RatFunc F :=
  ratFuncPreimage W (xCoord_nsmul_genericPoint_mem_ratFuncRange n)

open Classical in
@[simp] theorem algebraMap_nMulRatFunc [W.IsElliptic] (n : ℕ) :
    algebraMap (RatFunc F) W.FunctionField (nMulRatFunc W n)
      = (n • genericPoint (W := W)).xCoord :=
  algebraMap_ratFuncPreimage _

open Classical in
/-- **The validation at `n = 2`: `nMulRatFunc W 2 = doublingRatFunc W`.**

Both have the same image in `F(W)` — `algebraMap_doublingRatFunc` and
`xCoord_two_nsmul_genericPoint`, both merged — and `RatFunc F → F(W)` is injective, being a
homomorphism of fields.

⚠️ This is the check that the group-law construction produces the *same* rational function the
division polynomials do.  `n = 2` is one of the **two** indices at which the tree writes such a
fraction down; `nMulRatFunc_three` is the other.  It does not transport those formulæ's degrees:
`doublingRatFunc` is *defined* as `Φ₂/Ψ₂Sq` and `nMulRatFunc W 2` is now known to equal it, but
`nMulRatFunc W n` for `n ≠ 2, 3` has no such presentation. -/
theorem nMulRatFunc_two [W.IsElliptic] (h2 : (2 : F) ≠ 0) :
    nMulRatFunc W 2 = doublingRatFunc W := by
  refine (algebraMap (RatFunc F) W.FunctionField).injective ?_
  rw [algebraMap_nMulRatFunc, algebraMap_doublingRatFunc h2, xCoord_two_nsmul_genericPoint h2]

open Classical in
/-- **The validation at `n = 3`: `nMulRatFunc W 3 = triplingRatFunc W`.**

The same argument as `nMulRatFunc_two` against the merged `algebraMap_triplingRatFunc` and
`xCoord_three_nsmul_genericPoint` (`EllipticCurves.FunctionField.MulByThreeDegree` and
`…MulByNPullback`), and the reason this file imports `MulByThreeDegree` at all.

⚠️ `n = 2` and `n = 3` are the **only** indices at which the group-law construction can be checked
against a written-down fraction, because they are the only indices at which the tree writes one
down: `#682` and `#775` are the merged degree computations and there is no `Φₙ/ΨSqₙ` presentation
of `nMulRatFunc W n` at any other `n`.  That presentation at general `n` is `#404` / `#251`'s and
is what a degree count needs; see the module docstring. -/
theorem nMulRatFunc_three [W.IsElliptic] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    nMulRatFunc W 3 = triplingRatFunc W := by
  refine (algebraMap (RatFunc F) W.FunctionField).injective ?_
  rw [algebraMap_nMulRatFunc, algebraMap_triplingRatFunc h2 h3,
    xCoord_three_nsmul_genericPoint h2 h3]

/-! ### Non-vacuity

⚠️ Every statement above carries `[W.IsElliptic]`, `nMulRatFunc` is built from an inverse
isomorphism, and the chain runs through `negYAlgEquiv_ne_one`, so a curve on which the whole thing
elaborates with every instance discharged is worth committing rather than quoting.  The certificate
is over **`ℚ`** — deliberately not over an algebraically closed field, since nothing here needs
one — at `n = 5`, beyond the `2` and `3` at which the coordinate formulæ exist. -/

section Nonvacuity

/-- The curve `y² + y = x³` over `ℚ`, this development's standard certificate curve. -/
private noncomputable def exampleCurveXCoord : Affine ℚ := ⟨0, 0, 1, 0, 0⟩

private instance : exampleCurveXCoord.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurveXCoord, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

open Classical in
/-- **THE CERTIFICATE, part one.**  `x(5 • 𝒫)` is a rational function of `x` on a curve that
exists, over a field that is not algebraically closed. -/
example : (5 • genericPoint (W := exampleCurveXCoord)).xCoord ∈ ratFuncRange exampleCurveXCoord :=
  xCoord_nsmul_genericPoint_mem_ratFuncRange 5

open Classical in
/-- **THE CERTIFICATE, part two.**  And it has a name in `RatFunc ℚ`. -/
example : algebraMap (RatFunc ℚ) exampleCurveXCoord.FunctionField
      (nMulRatFunc exampleCurveXCoord 5)
    = (5 • genericPoint (W := exampleCurveXCoord)).xCoord :=
  algebraMap_nMulRatFunc 5

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
