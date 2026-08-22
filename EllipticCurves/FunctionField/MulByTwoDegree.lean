/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.RatFuncExtension
import EllipticCurves.FunctionField.MulByTwoExtensionFinite
import EllipticCurves.DivisionPolynomial.Coprime
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.FieldTheory.Relrank

/-!
# The degree of multiplication by two: `[F(W) : [2]∗F(W)] = 4`

Let `W` be an elliptic Weierstrass curve over a field `F` of characteristic `≠ 2`, with function
field `F(W)`, and let `[2]∗ = mulByTwoEndo h2 : F(W) →+* F(W)` be the multiplication-by-two
pullback.  This file computes

```
Module.finrank ↥[2]∗F(W) F(W) = 4,
```

i.e. `deg [2] = 4 = 2²` in the field-degree sense, and deduces the corollary that `[2]∗` is **not
surjective**.

Everything before this file gave only an upper bound: `MulByTwoFinite`'s
`mulByTwoEndo_isIntegralElem_genX` exhibits a monic quartic and `module_finite_mulByTwoRange`
concludes `Module.Finite`, with no lower bound whatsoever.

## The tower

Write `x = genX W`, `x₂ = [2]∗x = Φ₂(x)/Ψ₂Sq(x)`, and let `F(x) ⊆ F(W)` be the image of
`RatFunc F` under the algebra map built in `RatFuncExtension.lean`.  Then

```
                F(W)
             2 /    \ 4
          F(x)        [2]∗F(W)
             4 \    / 2
                F(x₂)
```

* `[F(W) : F(x)] = 2` is `finrank_ratFunc_functionField` (issue `#680`), transported along
  `AlgHom.equivFieldRange` to the subfield `F(x) ⊆ F(W)`;
* `[F(x) : F(x₂)] = max (deg Φ₂) (deg Ψ₂Sq) = max 4 3 = 4` is Mathlib's
  `RatFunc.finrank_eq_max_natDegree`, which needs the fraction `Φ₂/Ψ₂Sq` **in lowest terms** —
  that is `isCoprime_Φ_two_Ψ₂Sq` (issue `#681`), and it is where `[W.IsElliptic]` enters;
* `[[2]∗F(W) : F(x₂)] = 2` is the *transport* of the first line along `[2]∗`, which is a field
  isomorphism of `F(W)` onto `[2]∗F(W)` carrying `F(x)` onto `F(x₂)`.  It is **not** a computation
  inside `[2]∗F(W)`: that field is `F(x₂, y₂)`, and `F(x) ⊆ [2]∗F(W)` is false.
* Both diagonals compute `[F(W) : F(x₂)] = 8`, and cancelling the factor `2` gives the answer.

The bookkeeping is done with `IntermediateField.relfinrank`, whose two tower laws
(`relfinrank_mul_finrank_top`) and two transport lemmas (`relfinrank_map_map`,
`relfinrank_comap_comap_eq_relfinrank_of_le`) remove the need to build any `Algebra` instance
between the intermediate fields by hand.

## Retiring a caveat

`FunctionField/PlacePullback.lean`'s module docstring used to record that "*there is no proof that
`[2]∗` is non-surjective*", and therefore that its final section was only *conditionally* more
than a restatement of rung 5.  `not_surjective_mulByTwoEndo` below removes that caveat: `[2]∗` has
index four, so it is not an automorphism, the extension `F(W) / [2]∗F(W)` is proper, and the places
of `F(W)` really do lie over a strictly smaller function field.  That file's docstring now says so
and points here.

The removal is conditional on `[W.IsElliptic]`, and that is not bookkeeping: on a singular
Weierstrass curve the smooth locus is `𝔾ₘ` or `𝔾ₐ`, where multiplication by two is squaring (degree
two) or doubling (degree one, an isomorphism once `(2 : F) ≠ 0`).  `PlacePullback.lean`'s own
declarations carry no `IsElliptic`, so the two files state the dependence explicitly rather than
letting it be inferred.

## Main statements

* `RatFunc.natDegree_num_div_of_isCoprime`, `RatFunc.natDegree_denom_div_of_isCoprime` — for a
  coprime pair `p, q` the reduced numerator and denominator of `p / q : RatFunc F` have exactly the
  degrees of `p` and `q`.  General facts about `RatFunc`, proved here for want of a better home.
* `finrank_ratFuncRange` — `[F(W) : F(x)] = 2`, with `F(x)` realised as an intermediate field.
* `finrank_adjoin_doublingRatFunc` — `[F(x) : F(x₂)] = 4`.
* `finrank_mulByTwoFieldRange` — `[F(W) : [2]∗F(W)] = 4`, stated for the `AlgHom.fieldRange`.
* `finrank_mulByTwoRange_functionField` — **the headline**, stated for the `RingHom.range` that
  `module_finite_mulByTwoRange` and `PlacePullback.lean` use.
* `not_surjective_mulByTwoEndo` — `[2]∗` is not surjective.

## Scope

This is the field degree of `[2]`, i.e. `deg [n] = n²` at `n = 2` in the sense of Silverman
*AEC* II.2.  It is **not** a route to `#E[n] = n²`: the counting argument connecting the two — a
separable isogeny has as many points in its kernel as its degree — is nowhere in this tree, even
though the separability of `F(W) / [2]∗F(W)` now is (`MulByTwoGalois`, `#759`).  Do not assume the
step.  The full degree formula `∑_{p ↦ q} e_p · deg p = 4` is also out of scope here — this file
supplies its right-hand side, and the sum needs residue degrees (`#743`, `#749`) and a fundamental
identity (`EllipticCurves.FunctionField.PlaceRamificationInertia`, `#763`).  Those exist now; the
counting step of the previous sentence still does not.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2, III.4.10.
-/

open Module Polynomial IntermediateField

namespace RatFunc

variable {F : Type*} [Field F]

/-- For a coprime pair `p, q` with `q ≠ 0`, the reduced numerator and denominator of the rational
function `p / q` are associates of `p` and of `q`.

Both `p / q` and `num / denom` present the same element of `RatFunc F`, so `num * q = p * denom`;
each of the two coprimality hypotheses then turns one divisibility into the other. -/
private theorem associated_num_denom_div {p q : F[X]} (hq : q ≠ 0) (h : IsCoprime p q) :
    Associated (algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q).num p ∧
      Associated (algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q).denom q := by
  set r : RatFunc F := algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q with hr
  have hinj := IsFractionRing.injective F[X] (RatFunc F)
  have hqne : algebraMap F[X] (RatFunc F) q ≠ 0 := (map_ne_zero_iff _ hinj).2 hq
  have hdne : algebraMap F[X] (RatFunc F) r.denom ≠ 0 := (map_ne_zero_iff _ hinj).2 r.denom_ne_zero
  have h1 : algebraMap F[X] (RatFunc F) r.num / algebraMap F[X] (RatFunc F) r.denom
      = algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q := by
    rw [RatFunc.num_div_denom, hr]
  rw [div_eq_div_iff hdne hqne] at h1
  have key : r.num * q = p * r.denom := hinj (by rw [map_mul, map_mul]; exact h1)
  have hcnd : IsCoprime r.num r.denom := RatFunc.isCoprime_num_denom r
  exact ⟨associated_of_dvd_dvd (hcnd.dvd_of_dvd_mul_right ⟨q, key.symm⟩)
      (h.dvd_of_dvd_mul_right ⟨r.denom, key⟩),
    associated_of_dvd_dvd (hcnd.symm.dvd_of_dvd_mul_right ⟨p, by linear_combination key⟩)
      (h.symm.dvd_of_dvd_mul_right ⟨r.num, by linear_combination -key⟩)⟩

/-- **A coprime presentation is the reduced one, numerator half.**  `RatFunc.num_div` computes the
numerator only up to a division by `gcd p q`; when `p` and `q` are coprime that division changes
nothing, so the degree is exactly `p.natDegree`.  This is the form that
`RatFunc.finrank_eq_max_natDegree` has to be fed. -/
theorem natDegree_num_div_of_isCoprime {p q : F[X]} (hq : q ≠ 0) (h : IsCoprime p q) :
    (algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q).num.natDegree
      = p.natDegree :=
  natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (associated_num_denom_div hq h).1)

/-- **A coprime presentation is the reduced one, denominator half.** -/
theorem natDegree_denom_div_of_isCoprime {p q : F[X]} (hq : q ≠ 0) (h : IsCoprime p q) :
    (algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q).denom.natDegree
      = q.natDegree :=
  natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (associated_num_denom_div hq h).2)

end RatFunc

namespace WeierstrassCurve.Affine
namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

/-! ### The bottom of the tower: `F(x) ⊆ F(W)` -/

variable (W) in
/-- **The subfield `F(x) ⊆ F(W)`**: the image of `RatFunc F` under the algebra map of
`RatFuncExtension.lean`, as an intermediate field of `F(W) / F`. -/
noncomputable def ratFuncRange : IntermediateField F W.FunctionField :=
  (IsScalarTower.toAlgHom F (RatFunc F) W.FunctionField).fieldRange

/-- `F(x)` is generated by the generic `x`-coordinate: the image of `RatFunc F` is `F⟮genX W⟯`.
This is `RatFunc.adjoin_X` (`RatFunc F` is generated by its indeterminate) pushed forward, and it
is what makes `ratFuncRange` recognisable to the rest of the tree. -/
theorem ratFuncRange_eq_adjoin : ratFuncRange W = F⟮genX W⟯ := by
  rw [ratFuncRange, AlgHom.fieldRange_eq_map, ← RatFunc.adjoin_X (K := F),
    IntermediateField.adjoin_map]
  simp

/-- **`[F(W) : F(x)] = 2`**, the merged `finrank_ratFunc_functionField` transported from the
abstract `RatFunc F` to the subfield `F(x) ⊆ F(W)`. -/
theorem finrank_ratFuncRange : finrank ↥(ratFuncRange W) W.FunctionField = 2 := by
  have := Algebra.finrank_eq_of_equiv_equiv
    (R₀ := RatFunc F) (S₀ := W.FunctionField)
    (R₁ := ↥(ratFuncRange W)) (S₁ := W.FunctionField)
    (AlgHom.equivFieldRange (IsScalarTower.toAlgHom F (RatFunc F) W.FunctionField)).toRingEquiv
    (RingEquiv.refl _) (by ext f; rfl)
  rw [← this, finrank_ratFunc_functionField]

/-! ### The middle of the tower: `[F(x) : F(x₂)] = 4` -/

variable (W) in
/-- **The `x`-coordinate of the doubled generic point, as a rational function**: `Φ₂ / Ψ₂Sq` in
`RatFunc F`.  Its image in `F(W)` is `[2]∗ x` (`algebraMap_doublingRatFunc`). -/
noncomputable def doublingRatFunc : RatFunc F :=
  algebraMap F[X] (RatFunc F) (W.Φ 2) / algebraMap F[X] (RatFunc F) W.Ψ₂Sq

/-- The image of `doublingRatFunc` in `F(W)` is `[2]∗ x = Φ₂(x)/Ψ₂Sq(x)`, the `x`-coordinate of the
doubled generic point. -/
theorem algebraMap_doublingRatFunc (h2 : (2 : F) ≠ 0) :
    algebraMap (RatFunc F) W.FunctionField (doublingRatFunc W) = mulByTwoEndo h2 (genX W) := by
  rw [doublingRatFunc, map_div₀, algebraMap_ratFunc_algebraMap, algebraMap_ratFunc_algebraMap,
    mulByTwoEndo_genX, WeierstrassCurve.map_Φ, WeierstrassCurve.map_Ψ₂Sq, eval_map, eval_map,
    ← aeval_def, ← aeval_def, aeval_genX_eq_algebraMap, aeval_genX_eq_algebraMap]

/-- In characteristic `≠ 2` one has `(4 : F) ≠ 0`, the hypothesis under which `Ψ₂Sq` has its
expected degree three. -/
private lemma four_ne_zero_of_two_ne_zero (h2 : (2 : F) ≠ 0) : (4 : F) ≠ 0 := by
  intro h
  have h22 : (2 : F) * 2 = 0 := by linear_combination h
  rcases mul_eq_zero.mp h22 with h' | h' <;> exact h2 h'

/-- **`[F(x) : F(x₂)] = 4`.**  Mathlib's `RatFunc.finrank_eq_max_natDegree` computes the degree of
`F(X)` over the subfield generated by a rational function as the maximum of the degrees of its
*reduced* numerator and denominator.  Coprimality of `Φ₂` and `Ψ₂Sq` (issue `#681`, and the only
place `[W.IsElliptic]` is used in this file) says the presentation `Φ₂/Ψ₂Sq` is already reduced, and
the two degrees are `4` and `3`. -/
theorem finrank_adjoin_doublingRatFunc [W.IsElliptic] (h2 : (2 : F) ≠ 0) :
    finrank ↥(F⟮doublingRatFunc W⟯ : IntermediateField F (RatFunc F)) (RatFunc F) = 4 := by
  have h4 := four_ne_zero_of_two_ne_zero (F := F) h2
  have hq : W.Ψ₂Sq ≠ 0 := W.Ψ₂Sq_ne_zero h4
  rw [doublingRatFunc, RatFunc.finrank_eq_max_natDegree,
    RatFunc.natDegree_num_div_of_isCoprime hq W.isCoprime_Φ_two_Ψ₂Sq,
    RatFunc.natDegree_denom_div_of_isCoprime hq W.isCoprime_Φ_two_Ψ₂Sq,
    W.natDegree_Φ 2, W.natDegree_Ψ₂Sq h4]
  rfl

/-! ### The degree of multiplication by two -/

section Degree

variable [W.IsElliptic]

/-- **`[F(W) : [2]∗F(W)] = 4`**, stated for the range of `mulByTwoEndoAlgHom` as an intermediate
field.  See `finrank_mulByTwoRange_functionField` for the `RingHom.range` form.

The proof is the tower of the module docstring.  Writing `S = F(x₂)` for the image of `F(x)` under
`[2]∗`, the two decompositions of `[F(W) : S]` are

```
relfinrank S F(x)      * [F(W) : F(x)]      = 4 * 2 = 8,
relfinrank S [2]∗F(W)  * [F(W) : [2]∗F(W)]  = 2 * ?,
```

and the second factor of the second line is the answer.  Both `relfinrank`s are computed by
transport: the first by pulling the pair `(S, F(x))` back along `F(x) ≅ RatFunc F`, where it becomes
`(F⟮Φ₂/Ψ₂Sq⟯, ⊤)`; the second by pushing the pair `(F(x), ⊤)` forward along the injection `[2]∗`. -/
theorem finrank_mulByTwoFieldRange (h2 : (2 : F) ≠ 0) :
    finrank ↥(mulByTwoEndoAlgHom (W := W) h2).fieldRange W.FunctionField = 4 := by
  set σ := mulByTwoEndoAlgHom (W := W) h2 with hσ
  set ι := IsScalarTower.toAlgHom F (RatFunc F) W.FunctionField with hι
  set S := (ratFuncRange W).map σ with hSdef
  have hSadj : S = F⟮σ (genX W)⟯ := by
    rw [hSdef, ratFuncRange_eq_adjoin, IntermediateField.adjoin_map, Set.image_singleton]
  have hd : ι (doublingRatFunc W) = σ (genX W) := algebraMap_doublingRatFunc h2
  have hSmap : S = (F⟮doublingRatFunc W⟯).map ι := by
    rw [IntermediateField.adjoin_map, Set.image_singleton, hd, hSadj]
  -- `S = F(x₂)` sits inside both `F(x)` and `[2]∗F(W)`
  have hSFx : S ≤ ratFuncRange W := by
    rw [hSadj, IntermediateField.adjoin_simple_le_iff, ← hd]
    exact ⟨doublingRatFunc W, rfl⟩
  have hSA : S ≤ σ.fieldRange := by
    rw [hSdef, AlgHom.fieldRange_eq_map]
    exact IntermediateField.map_mono σ le_top
  -- `[F(x) : F(x₂)] = 4`, by pulling back along `F(x) ≅ RatFunc F`
  have hrel1 : relfinrank S (ratFuncRange W) = 4 := by
    rw [← IntermediateField.relfinrank_comap_comap_eq_relfinrank_of_le S (ratFuncRange W) ι le_rfl]
    have hc1 : (ratFuncRange W).comap ι = ⊤ := by
      rw [eq_top_iff]; intro x _; exact ⟨x, rfl⟩
    have hc2 : S.comap ι = F⟮doublingRatFunc W⟯ := by rw [hSmap, IntermediateField.comap_map]
    rw [hc1, hc2, IntermediateField.relfinrank_top_right, finrank_adjoin_doublingRatFunc h2]
  -- `[[2]∗F(W) : F(x₂)] = 2`, by pushing `(F(x), ⊤)` forward along `[2]∗`
  have hrel2 : relfinrank S σ.fieldRange = 2 := by
    rw [hSdef, AlgHom.fieldRange_eq_map, IntermediateField.relfinrank_map_map,
      IntermediateField.relfinrank_top_right, finrank_ratFuncRange]
  have h8 : finrank ↥S W.FunctionField = 8 := by
    rw [← IntermediateField.relfinrank_mul_finrank_top hSFx, hrel1, finrank_ratFuncRange]
  have hfin := IntermediateField.relfinrank_mul_finrank_top hSA
  rw [hrel2, h8] at hfin
  omega

/-- **The degree of multiplication by two: `[F(W) : [2]∗F(W)] = 4`.**

This is the first lower bound on `deg [2]` in this tree: `MulByTwoFinite` /
`MulByTwoExtensionFinite` give only "finite, of degree `≤ 4`" from a monic quartic.  The subring
and the algebra instance are the ones `module_finite_mulByTwoRange` uses, so the two statements
compose. -/
theorem finrank_mulByTwoRange_functionField (h2 : (2 : F) ≠ 0) :
    letI : Algebra ↥(mulByTwoEndo (W := W) h2).range W.FunctionField :=
      ((mulByTwoEndo (W := W) h2).range.subtype).toAlgebra
    finrank ↥(mulByTwoEndo (W := W) h2).range W.FunctionField = 4 := by
  letI : Algebra ↥(mulByTwoEndo (W := W) h2).range W.FunctionField :=
    ((mulByTwoEndo (W := W) h2).range.subtype).toAlgebra
  have hmem : ∀ z : W.FunctionField,
      z ∈ (mulByTwoEndoAlgHom (W := W) h2).fieldRange ↔ z ∈ (mulByTwoEndo (W := W) h2).range :=
    fun _ => Iff.rfl
  let i : ↥(mulByTwoEndoAlgHom (W := W) h2).fieldRange ≃+* ↥(mulByTwoEndo (W := W) h2).range :=
    { toFun := fun a => ⟨a.1, (hmem a.1).mp a.2⟩
      invFun := fun a => ⟨a.1, (hmem a.1).mpr a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  rw [← Algebra.finrank_eq_of_equiv_equiv i (RingEquiv.refl W.FunctionField) (by ext a; rfl),
    finrank_mulByTwoFieldRange h2]

/-- **`[2]∗` is not surjective.**  A surjective endomorphism would have `fieldRange = ⊤`, hence
index one, contradicting index four.

This is the statement `FunctionField/PlacePullback.lean` asks for by name: it is what makes that
file's final section unconditionally more than a restatement of rung 5, since `F(W)` is now known to
be a proper extension of `[2]∗F(W)`. -/
theorem not_surjective_mulByTwoEndo (h2 : (2 : F) ≠ 0) :
    ¬ Function.Surjective (mulByTwoEndo (W := W) h2) := by
  intro hs
  have htop : (mulByTwoEndoAlgHom (W := W) h2).fieldRange = ⊤ := AlgHom.fieldRange_eq_top.mpr hs
  have h4 := finrank_mulByTwoFieldRange (W := W) h2
  rw [htop, ← IntermediateField.relfinrank_top_right (⊤ : IntermediateField F W.FunctionField),
    IntermediateField.relfinrank_self] at h4
  exact absurd h4 (by norm_num)

end Degree

/-! ### Non-vacuity

`y² = x³ - x` over `ℚ`, of discriminant `64` — the curve `#668` and `#675` instantiate on.  Both
hypotheses of the section above are discharged: it is elliptic, and `(2 : ℚ) ≠ 0`. -/

section Nonvacuity

/-- The curve `y² = x³ - x` over `ℚ`, of discriminant `64`. -/
private def exampleCurve : Affine ℚ := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

example :
    letI : Algebra ↥(mulByTwoEndo (W := exampleCurve) (by norm_num)).range
        exampleCurve.FunctionField :=
      ((mulByTwoEndo (W := exampleCurve) (by norm_num)).range.subtype).toAlgebra
    finrank ↥(mulByTwoEndo (W := exampleCurve) (by norm_num)).range
      exampleCurve.FunctionField = 4 :=
  finrank_mulByTwoRange_functionField _

example : ¬ Function.Surjective (mulByTwoEndo (W := exampleCurve) (by norm_num)) :=
  not_surjective_mulByTwoEndo _

end Nonvacuity

end CoordinateRing
end WeierstrassCurve.Affine
