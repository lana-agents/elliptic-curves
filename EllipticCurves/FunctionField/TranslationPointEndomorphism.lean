/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.TranslationAutomorphism
import EllipticCurves.FunctionField.WeilPairingBilinearBaseField

/-!
# `τ_P` for a point that may be `O`: `translatePointEndo : W.Point → (F(W) →+* F(W))`

`EllipticCurves.FunctionField.TranslationEndomorphism` builds translation by a point as

```
translateEndo (h₂ : W.Equation x₂ y₂) : W.FunctionField →+* W.FunctionField
```

indexed by an **affine equation point**.  So `τ_O` — translation by the point at infinity, which is
the identity and needs no proof — is not expressible by it.

That is harmless for every merged consumer, each of which translates by a single affine point.  It
stops being harmless in the product

```
h := ∏_{i=0}^{n-1} g_T ∘ τ_{[i]P}
```

of Silverman *AEC* III.8.1(d) (`#465` deliverable 2): the `i = 0` factor is `τ_O`, and for `n > 2`
the point `[i]P` can be `O` for `0 < i < n` as well — take `n = 6` and `ord P = 4`, where `[4]P = O`
occurs inside the product although `T = [6]P = [2]P ≠ O` is a legitimate `6`-torsion point.  So it
is not a degenerate case that the hypotheses rule out.

⚠️ **`n = 2` does not need this file.**  There the product is `g_T · (g_T ∘ τ_P)`, whose `i = 0`
factor is literally `g_T`; the `n = 2` alternating property (`#688`) is not blocked on anything
here.

## Main definitions and results

* `translatePointEndo` — translation by an arbitrary `P : W.Point`, with `translatePointEndo 0` the
  identity and `translatePointEndo (Point.some x y h) = translateEndo h.left`, both `rfl` and both
  `@[simp]`.  `translatePointEndo_torsionPoint` is the bridge for a consumer holding a
  `W.Equation`;
* `translatePointEndo_comp` — `τ_P∗ ∘ τ_Q∗ = τ_{P+Q}∗`, the composition law with **no side
  condition** and no case analysis left to the caller;
* `translatePointMonoidHom` — the same law packaged as a monoid homomorphism
  `Multiplicative W.Point →* (F(W) →+* F(W))` (multiplication of ring endomorphisms *is*
  composition, `RingHom.mul_def`), which is what makes the iterated forms free;
* `translatePointEndo_nsmul` — `τ_{n • P}∗ = (τ_P∗) ^ n`, and `translatePointEndo_nsmul_apply` its
  `Function.iterate` form, which is the shape the product above consumes;
* `translatePointEndo_mul_neg`, `translatePointEndo_bijective` — `τ_{-P}∗` is the two-sided inverse.

## Where the content is

Only the `some/some` case of `translatePointEndo_comp` has any content, and it splits again on
whether `P + Q` is `O`:

* `P + Q = O` is the merged `translateEndo_comp_zero` (`TranslationAutomorphism.lean`), which is
  *not* an instance of the general composition law — it is what
  `translateEndo_surjective`/`translateAlgEquiv` are already built from;
* `P + Q` affine is the merged `translateEndo_comp` (`TranslationComposition.lean`), whose
  hypothesis lives at the `F(W)`-point level and is fed from the base-field relation by the merged
  `translatePoint_add` (`WeilPairingBilinearBaseField.lean`).

Collecting the three branches once, here, is the point: a caller writing a product over `⟨P⟩` would
otherwise have to redo this split at every use site, and the `P + Q = O` branch is exactly the one
that is easy to forget.

## Scope

* No translation by a point of `W` over a **larger** field.  That is `#679` Route B (priced there
  at 10 files / 132 declarations) and it is not what the `n = 2` alternating property needs.
* No restatement of the merged `translateEndo` API in `Point` form; the existing lemmas are reached
  through `translatePointEndo_some` / `translatePointEndo_torsionPoint`.
* Nothing about `[n]∗`, `#418`, the alternating property itself, or Ward.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.
-/

open Polynomial

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic] {x y : F}

/-! ### The definition -/

/-- **Translation by an arbitrary point of `W`.**  At the point at infinity it is the identity; at
an affine point it is the merged `translateEndo`.  The `W.Equation` datum `translateEndo` needs is
extracted from the `Nonsingular` field of `Point.some`. -/
noncomputable def translatePointEndo : W.Point → (W.FunctionField →+* W.FunctionField)
  | .zero => RingHom.id _
  | .some _ _ h => translateEndo h.left

@[simp] lemma translatePointEndo_zero :
    translatePointEndo (0 : W.Point) = RingHom.id W.FunctionField := rfl

@[simp] lemma translatePointEndo_some (h : W.Nonsingular x y) :
    translatePointEndo (Point.some x y h) = translateEndo h.left := rfl

/-- The bridge for a consumer holding a `W.Equation`: `torsionPoint` is the `W.Point` it names, and
`translatePointEndo` at it is the `translateEndo` every merged lemma is stated about. -/
lemma translatePointEndo_torsionPoint (h : W.Equation x y) :
    translatePointEndo (torsionPoint h) = translateEndo h := rfl

/-! ### The composition law -/

open Classical in
/-- **`τ_P∗ ∘ τ_Q∗ = τ_{P+Q}∗`, with no side condition.**  The three branches — either point at
infinity, `P + Q = O`, `P + Q` affine — are discharged here once and for all; see the module
docstring for which merged lemma each uses. -/
theorem translatePointEndo_comp (P Q : W.Point) :
    (translatePointEndo P).comp (translatePointEndo Q) = translatePointEndo (P + Q) := by
  have hz : (Point.zero : W.Point) = 0 := rfl
  match P, Q with
  | .zero, Q => rw [hz, translatePointEndo_zero, RingHom.id_comp, zero_add]
  | .some xP yP hP, .zero => rw [hz, translatePointEndo_zero, RingHom.comp_id, add_zero]
  | .some xP yP hP, .some xQ yQ hQ =>
      rcases hsum : (Point.some xP yP hP + Point.some xQ yQ hQ : W.Point) with _ | ⟨xR, yR, hR⟩
      · have h0 : translatePoint hP.left + translatePoint hQ.left = 0 := by
          rw [← torsionPointMap_torsionPoint hP.left, ← torsionPointMap_torsionPoint hQ.left,
            ← map_add, show torsionPoint hP.left + torsionPoint hQ.left = 0 from hsum, map_zero]
        rw [translatePointEndo_some, translatePointEndo_some,
          translateEndo_comp_zero hP.left hQ.left h0]
        rfl
      · have hadd : torsionPoint hP.left + torsionPoint hQ.left = torsionPoint hR.left := hsum
        rw [translatePointEndo_some, translatePointEndo_some, translatePointEndo_some,
          translateEndo_comp hP.left hQ.left hR.left (translatePoint_add _ _ _ hadd)]

open Classical in
/-- The composition law in the multiplicative notation of `RingHom.instMonoid`, where the product of
two ring endomorphisms *is* their composite (`RingHom.mul_def`). -/
theorem translatePointEndo_mul (P Q : W.Point) :
    translatePointEndo P * translatePointEndo Q = translatePointEndo (P + Q) :=
  translatePointEndo_comp P Q

open Classical in
/-- The composition law in applied form. -/
theorem translatePointEndo_apply_apply (P Q : W.Point) (f : W.FunctionField) :
    translatePointEndo P (translatePointEndo Q f) = translatePointEndo (P + Q) f := by
  have h := translatePointEndo_comp P Q
  exact congr($h f)

open Classical in
/-- **`P ↦ τ_P∗` is a monoid homomorphism** from `W.Point` (written multiplicatively) to the
endomorphism monoid of `F(W)`.  Everything iterated below is `map_pow` of this. -/
noncomputable def translatePointMonoidHom :
    Multiplicative W.Point →* (W.FunctionField →+* W.FunctionField) where
  toFun P := translatePointEndo P.toAdd
  map_one' := translatePointEndo_zero
  map_mul' _ _ := (translatePointEndo_comp _ _).symm

@[simp] lemma translatePointMonoidHom_apply (P : Multiplicative W.Point) :
    translatePointMonoidHom P = translatePointEndo P.toAdd := rfl

/-! ### Iterating

The product `∏_{i=0}^{n-1} g ∘ τ_{[i]P}` translates by the successive multiples of a single point,
so what it needs is `τ_{n • P}∗` in terms of `τ_P∗`. -/

open Classical in
/-- **`τ_{n • P}∗ = (τ_P∗) ^ n`.** -/
theorem translatePointEndo_nsmul (n : ℕ) (P : W.Point) :
    translatePointEndo (n • P) = translatePointEndo P ^ n := by
  induction n with
  | zero => rw [zero_smul, translatePointEndo_zero, pow_zero]; rfl
  | succ n ih => rw [succ_nsmul, ← translatePointEndo_mul, ih, pow_succ]

open Classical in
/-- `τ_{n • P}∗` as an `n`-fold iterate — the `Function.iterate` form, since `RingHom.coe_pow`
identifies the monoid power with it. -/
theorem translatePointEndo_nsmul_apply (n : ℕ) (P : W.Point) (f : W.FunctionField) :
    translatePointEndo (n • P) f = (translatePointEndo P)^[n] f := by
  rw [translatePointEndo_nsmul, RingHom.coe_pow]

/-! ### Invertibility -/

open Classical in
/-- **`τ_{-P}∗` is the right inverse of `τ_P∗`.** -/
@[simp] theorem translatePointEndo_mul_neg (P : W.Point) :
    translatePointEndo P * translatePointEndo (-P) = 1 := by
  rw [translatePointEndo_mul, add_neg_cancel, translatePointEndo_zero]; rfl

open Classical in
/-- **`τ_{-P}∗` is the left inverse of `τ_P∗`.** -/
@[simp] theorem translatePointEndo_neg_mul (P : W.Point) :
    translatePointEndo (-P) * translatePointEndo P = 1 := by
  rw [translatePointEndo_mul, neg_add_cancel, translatePointEndo_zero]; rfl

open Classical in
/-- **Translation by any point is bijective on `F(W)`**, with explicit inverse `τ_{-P}∗`.  The
merged `translateEndo_bijective` is the affine case. -/
theorem translatePointEndo_bijective (P : W.Point) :
    Function.Bijective (translatePointEndo P) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨translatePointEndo (-P), fun f => ?_, fun f => ?_⟩
  · rw [translatePointEndo_apply_apply, neg_add_cancel, translatePointEndo_zero, RingHom.id_apply]
  · rw [translatePointEndo_apply_apply, add_neg_cancel, translatePointEndo_zero, RingHom.id_apply]

/-! ### Non-vacuity

`translatePointEndo` is total on `W.Point`, so nothing above can be vacuous for lack of a point;
what is worth exhibiting is the `some + some = some` branch of the composition law on a curve where
it is not the degenerate one.  On `y² = x³ - x` over `ℚ` — the curve the rest of this subtree uses —
every affine rational point is `2`-torsion, so `P + P = O` there and only the `P + Q = O` branch
would be exercised.  Here `P = (2, 3)` on `y² = x³ + 1` has `[2]P = (0, 1)`, affine. -/

section Nonvacuity

/-- The curve `y² = x³ + 1` over `ℚ`, of discriminant `-432`. -/
private def exampleCurve : Affine ℚ := ⟨0, 0, 0, 0, 1⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleNonsingularP : exampleCurve.Nonsingular 2 3 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

private lemma exampleNonsingularT : exampleCurve.Nonsingular 0 1 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `[2](2, 3) = (0, 1)` on `y² = x³ + 1`: the tangent has slope `2`, so `x(2P) = 4 - 4 = 0`. -/
private lemma exampleDouble :
    Point.some (2 : ℚ) 3 exampleNonsingularP + Point.some (2 : ℚ) 3 exampleNonsingularP
      = Point.some (0 : ℚ) 1 exampleNonsingularT := by
  have hy : (3 : ℚ) ≠ exampleCurve.negY 2 3 := by
    norm_num [exampleCurve, WeierstrassCurve.Affine.negY]
  rw [Point.add_self_of_Y_ne hy, Point.some.injEq]
  constructor <;>
    norm_num [exampleCurve, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.slope]

-- The `convert` is bookkeeping, not mathematics: `translatePointEndo_mul` is stated
-- `open Classical in`, so the `+` in its right-hand side carries `Classical.propDecidable`, while
-- `exampleDouble` — elaborated at `F = ℚ`, where a `DecidableEq` instance exists — carries
-- `instDecidableEqRat`.  `convert ... using 4` closes the gap by `Subsingleton.elim` on the two
-- `DecidableEq ℚ` instances.
open Classical in
example : translatePointEndo (Point.some (2 : ℚ) 3 exampleNonsingularP)
      * translatePointEndo (Point.some (2 : ℚ) 3 exampleNonsingularP)
    = translatePointEndo (Point.some (0 : ℚ) 1 exampleNonsingularT) := by
  rw [translatePointEndo_mul]
  exact congrArg translatePointEndo (by convert exampleDouble using 4)

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
