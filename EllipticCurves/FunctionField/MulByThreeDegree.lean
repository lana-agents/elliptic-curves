/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByTwoDegree
import EllipticCurves.FunctionField.MulByThreeExtensionFinite

/-!
# The degree of multiplication by three: `[F(W) : [3]∗F(W)] = 9`

Let `W` be an elliptic Weierstrass curve over a field `F` with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, with
function field `F(W)`, and let `[3]∗ = mulByThreeEndo h2 h3 : F(W) →+* F(W)` be the
multiplication-by-three pullback.  This file computes

```
Module.finrank ↥[3]∗F(W) F(W) = 9,
```

i.e. `deg [3] = 9 = 3²` in the field-degree sense, and deduces that `[3]∗` is **not surjective**.

Everything before this file gave only an upper bound: `MulByThreeFinite`'s
`mulByThreeEndo_isIntegralElem_genX` exhibits a monic polynomial of degree nine and
`module_finite_mulByThreeRange` concludes `Module.Finite`, with no lower bound whatsoever.

## The tower, and what is reused verbatim

Write `x = genX W`, `x₃ = [3]∗x = Φ₃(x)/ΨSq₃(x)`, and let `F(x) ⊆ F(W)` be the image of `RatFunc F`.

```
                F(W)
             2 /    \ 9
          F(x)        [3]∗F(W)
             9 \    / 2
                F(x₃)
```

This is `MulByTwoDegree`'s diagram with `4` replaced by `9`, and it is *literally* that file's
argument — **including the proof**.  `ratFuncRange`, `finrank_ratFuncRange`, the two `RatFunc`
degree lemmas (`RatFunc.natDegree_num_div_of_isCoprime`, `RatFunc.natDegree_denom_div_of_isCoprime`)
and the whole tower `finrank_fieldRange_eq_finrank_adjoin` are `n`-independent and are imported
rather than restated — which is why this file imports `MulByTwoDegree` even though nothing about
`[2]` is used.  Only the middle degree changes, and after the tower was extracted that is visible in
the proof term of `finrank_mulByThreeFieldRange`, which is two lines long:

* `[F(x) : F(x₃)] = max (deg Φ₃) (deg ΨSq₃) = max 9 8 = 9` by
  `RatFunc.finrank_eq_max_natDegree`, which needs `Φ₃/ΨSq₃` **in lowest terms**;
* both diagonals compute `[F(W) : F(x₃)] = 18`, and cancelling the factor `2` gives the answer.

⚠️ `[3]∗F(W) = F(x₃, y₃)` is **not** `F(x₃)`, and `F(x) ⊆ [3]∗F(W)` is false.  The right-hand
edge `[[3]∗F(W) : F(x₃)] = 2` is the *transport* of `[F(W) : F(x)] = 2` along `[3]∗`, which is a
field isomorphism of `F(W)` onto its range carrying `F(x)` onto `F(x₃)` — not a computation inside
`[3]∗F(W)`.  `IntermediateField.relfinrank` and its two transport lemmas do that bookkeeping.

## The one genuinely new input

`isCoprime_Φ_three_ΨSq_three` (`EllipticCurves.DivisionPolynomial.Coprime`).  The `n = 2`
certificate `isCoprime_Φ_two_Ψ₂Sq` is an explicit Bézout identity over `Δ²`; the same route at
`n = 3` is a `17 × 17` Sylvester matrix and is not viable.  What replaces it is the congruence
`preΨ₄² ≡ Ψ₂Sq⁴ (mod Ψ₃)`, i.e. `ψ₂(2P) = ψ₄(P)/ψ₂(P)⁴` read univariately — see that file.

## Main statements

* `triplingRatFunc` and `algebraMap_triplingRatFunc` — the `RatFunc F` presentation of `x₃`;
* `finrank_adjoin_triplingRatFunc` — `[F(x) : F(x₃)] = 9`;
* `finrank_mulByThreeFieldRange` — `[F(W) : [3]∗F(W)] = 9`, for the `AlgHom.fieldRange`;
* `finrank_mulByThreeRange_functionField` — **the headline**, for the `RingHom.range` that
  `module_finite_mulByThreeRange` uses;
* `not_surjective_mulByThreeEndo` — `[3]∗` is not surjective.

## Scope

This is the field degree of `[3]`, i.e. `deg [n] = n²` at `n = 3` in the sense of Silverman
*AEC* II.2 / III.4.10.  It is **not** a route to `#E[3] = 9`: that count is already merged, by a
different argument (`card_torsion_three`, `EllipticCurves.Torsion.ThreeTorsionStructure`, over an
algebraically closed base), and the step that would connect the two — a separable isogeny has as
many points in its kernel as its degree — is nowhere in this tree.  Do not assume it in either
direction; in particular nothing here re-proves the count, and the count does not shorten anything
here.

Also **not** here: the `n = 3` mirror of `MulByTwoGalois` (`#759`), which is how the consumer
(`#419`, non-degeneracy of `e_n` at `n = 3`) reaches this degree.  That chain lives in
`EllipticCurves.FunctionField.TranslationActionThree` (the `E[3]`-translation action
`TorsionThreeMul`, its `MulSemiringAction` and `FaithfulSMul`, and `card_torsionThreeMul = 9`) and
`EllipticCurves.FunctionField.MulByThreeGalois` (Artin's `finrank_fixedFieldThree = 9`, the
sandwich `fixedFieldThree = [3]∗F(W)`, and `IsGalois`).  Both consume the degree proved below;
nothing below consumes them.

`EllipticCurves.FunctionField.WeilPairing`'s scope section is the canonical account of that chain
and of what still gates non-degeneracy at each `n`; read it there rather than here.

⚠️ Earlier versions of this paragraph **quoted** that section in order to report which of its
clauses had gone stale, and had to be rewritten twice in one evening as a result — once when the
degree below landed and once when `TranslationActionThree` did.  A verbatim quote is a second copy
with every drift property `#769` removed nineteen of.  Point at the canonical section; do not
restate it.

⚠️ `[W.IsElliptic]` is required and is not bookkeeping: it is what makes `Δ` a unit and hence
`Φ₃`/`ΨSq₃` coprime.  On a singular Weierstrass curve the smooth locus is `𝔾ₘ` or `𝔾ₐ`, where
multiplication by three has degree three, or degree one once `(3 : F) ≠ 0`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2, III.4.10.
-/

open Module Polynomial IntermediateField

namespace WeierstrassCurve.Affine
namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

/-! ### The middle of the tower: `[F(x) : F(x₃)] = 9` -/

variable (W) in
/-- **The `x`-coordinate of the tripled generic point, as a rational function**: `Φ₃ / ΨSq₃` in
`RatFunc F`.  Its image in `F(W)` is `[3]∗ x` (`algebraMap_triplingRatFunc`). -/
noncomputable def triplingRatFunc : RatFunc F :=
  algebraMap F[X] (RatFunc F) (W.Φ 3) / algebraMap F[X] (RatFunc F) (W.ΨSq 3)

/-- The image of `triplingRatFunc` in `F(W)` is `[3]∗ x = Φ₃(x)/ΨSq₃(x)`, the `x`-coordinate of the
tripled generic point. -/
theorem algebraMap_triplingRatFunc (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    algebraMap (RatFunc F) W.FunctionField (triplingRatFunc W) = mulByThreeEndo h2 h3 (genX W) := by
  rw [triplingRatFunc, map_div₀, algebraMap_ratFunc_algebraMap, algebraMap_ratFunc_algebraMap,
    mulByThreeEndo_genX, WeierstrassCurve.map_Φ, WeierstrassCurve.map_ΨSq, eval_map, eval_map,
    ← aeval_def, ← aeval_def, aeval_genX_eq_algebraMap, aeval_genX_eq_algebraMap]

/-- **`[F(x) : F(x₃)] = 9`.**  Mathlib's `RatFunc.finrank_eq_max_natDegree` computes the degree of
`F(X)` over the subfield generated by a rational function as the maximum of the degrees of its
*reduced* numerator and denominator.  Coprimality of `Φ₃` and `ΨSq₃` (the only place
`[W.IsElliptic]` is used in this file) says the presentation `Φ₃/ΨSq₃` is already reduced, and the
two degrees are `natDegree (Φ 3) = 3² = 9` and `natDegree (ΨSq 3) = 3² - 1 = 8`. -/
theorem finrank_adjoin_triplingRatFunc [W.IsElliptic] (h3 : (3 : F) ≠ 0) :
    finrank ↥(F⟮triplingRatFunc W⟯ : IntermediateField F (RatFunc F)) (RatFunc F) = 9 := by
  have h3' : ((3 : ℤ) : F) ≠ 0 := by exact_mod_cast h3
  have hq : W.ΨSq 3 ≠ 0 := W.ΨSq_ne_zero h3'
  rw [triplingRatFunc, RatFunc.finrank_eq_max_natDegree,
    RatFunc.natDegree_num_div_of_isCoprime hq W.isCoprime_Φ_three_ΨSq_three,
    RatFunc.natDegree_denom_div_of_isCoprime hq W.isCoprime_Φ_three_ΨSq_three,
    W.natDegree_Φ 3, W.natDegree_ΨSq h3']
  rfl

/-! ### The degree of multiplication by three -/

section Degree

variable [W.IsElliptic]

/-- **`[F(W) : [3]∗F(W)] = 9`**, stated for the range of `mulByThreeEndoAlgHom` as an intermediate
field.  See `finrank_mulByThreeRange_functionField` for the `RingHom.range` form.

The proof is the tower of the module docstring, and it is *not* written out here: it is
`finrank_fieldRange_eq_finrank_adjoin` (`EllipticCurves.FunctionField.MulByTwoDegree`), at
`σ = [3]∗` and `r = Φ₃/ΨSq₃`, composed with the middle degree `finrank_adjoin_triplingRatFunc`.
Only the middle degree distinguishes this from `finrank_mulByTwoFieldRange`, and after the shared
tower was extracted that is visible in the proof term rather than only in prose. -/
theorem finrank_mulByThreeFieldRange (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    finrank ↥(mulByThreeEndoAlgHom (W := W) h2 h3).fieldRange W.FunctionField = 9 := by
  rw [finrank_fieldRange_eq_finrank_adjoin _ _ (algebraMap_triplingRatFunc h2 h3),
    finrank_adjoin_triplingRatFunc h3]

/-- **The degree of multiplication by three: `[F(W) : [3]∗F(W)] = 9`.**

This is the first lower bound on `deg [3]` in this tree: `MulByThreeFinite` /
`MulByThreeExtensionFinite` give only "finite, of degree `≤ 9`" from a monic degree-nine
polynomial.  The subring and the algebra instance are the ones `module_finite_mulByThreeRange` uses,
so the two statements compose. -/
theorem finrank_mulByThreeRange_functionField (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    letI : Algebra ↥(mulByThreeEndo (W := W) h2 h3).range W.FunctionField :=
      ((mulByThreeEndo (W := W) h2 h3).range.subtype).toAlgebra
    finrank ↥(mulByThreeEndo (W := W) h2 h3).range W.FunctionField = 9 := by
  letI : Algebra ↥(mulByThreeEndo (W := W) h2 h3).range W.FunctionField :=
    ((mulByThreeEndo (W := W) h2 h3).range.subtype).toAlgebra
  have hmem : ∀ z : W.FunctionField,
      z ∈ (mulByThreeEndoAlgHom (W := W) h2 h3).fieldRange ↔
        z ∈ (mulByThreeEndo (W := W) h2 h3).range :=
    fun _ => Iff.rfl
  let i : ↥(mulByThreeEndoAlgHom (W := W) h2 h3).fieldRange ≃+*
      ↥(mulByThreeEndo (W := W) h2 h3).range :=
    { toFun := fun a => ⟨a.1, (hmem a.1).mp a.2⟩
      invFun := fun a => ⟨a.1, (hmem a.1).mpr a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  rw [← Algebra.finrank_eq_of_equiv_equiv i (RingEquiv.refl W.FunctionField) (by ext a; rfl),
    finrank_mulByThreeFieldRange h2 h3]

/-- **`[3]∗` is not surjective.**  A surjective endomorphism would have `fieldRange = ⊤`, hence
index one, contradicting index nine.  The `n = 2` counterpart is `not_surjective_mulByTwoEndo`. -/
theorem not_surjective_mulByThreeEndo (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ¬ Function.Surjective (mulByThreeEndo (W := W) h2 h3) := by
  intro hs
  have htop : (mulByThreeEndoAlgHom (W := W) h2 h3).fieldRange = ⊤ :=
    AlgHom.fieldRange_eq_top.mpr hs
  have h9 := finrank_mulByThreeFieldRange (W := W) h2 h3
  rw [htop, ← IntermediateField.relfinrank_top_right (⊤ : IntermediateField F W.FunctionField),
    IntermediateField.relfinrank_self] at h9
  exact absurd h9 (by norm_num)

end Degree

/-! ### Non-vacuity

`y² = x³ - x` over `ℚ`, of discriminant `64` — the curve `MulByTwoDegree` instantiates on, and
`ℚ` rather than `AlgebraicClosure ℚ` deliberately: nothing above needs an algebraically closed base.
All three hypotheses are discharged: it is elliptic, `(2 : ℚ) ≠ 0` and `(3 : ℚ) ≠ 0`. -/

section Nonvacuity

/-- The curve `y² = x³ - x` over `ℚ`, of discriminant `64`. -/
private def exampleCurve : Affine ℚ := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

example :
    letI : Algebra ↥(mulByThreeEndo (W := exampleCurve) (by norm_num) (by norm_num)).range
        exampleCurve.FunctionField :=
      ((mulByThreeEndo (W := exampleCurve) (by norm_num)
        (by norm_num)).range.subtype).toAlgebra
    finrank ↥(mulByThreeEndo (W := exampleCurve) (by norm_num) (by norm_num)).range
      exampleCurve.FunctionField = 9 :=
  finrank_mulByThreeRange_functionField _ _

example : ¬ Function.Surjective
    (mulByThreeEndo (W := exampleCurve) (by norm_num) (by norm_num)) :=
  not_surjective_mulByThreeEndo _ _

end Nonvacuity

end CoordinateRing
end WeierstrassCurve.Affine
