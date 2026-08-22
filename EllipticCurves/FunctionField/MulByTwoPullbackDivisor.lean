/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByTwoPlaceAtInfinity
import EllipticCurves.FunctionField.PullbackDivisor

/-!
# The first computed coefficient of a pulled-back divisor

`EllipticCurves.FunctionField.PullbackDivisor` builds `[2]∗` as a map of divisors, with every
coefficient abstract:

```lean
pullbackDivisorTwo_apply :
    pullbackDivisorTwo h2 D p = ramificationIdxTwo h2 p * D (comapProjPointTwo h2 p)
```

and `EllipticCurves.FunctionField.MulByTwoPlaceAtInfinity` computes *both* factors at the point at
infinity — `comapProjPointTwo h2 none = none` and `ramificationIdxTwo h2 none = 1`.  Neither file
imports the other, so the corollary has nowhere to live but here.

## Main result

* `WeierstrassCurve.Affine.CoordinateRing.pullbackDivisorTwo_apply_none` —
  `pullbackDivisorTwo h2 D none = D none`.

**This is the first coefficient of a pulled-back divisor that this tree computes.**  Every earlier
statement about `[2]∗` on divisors reads `e_p · D (comap p)` with both factors opaque; this one is
an identity between the input and the output divisor.

What it is *not*: it is not the degree formula `∑_{p ↦ q} e_p · deg p = 4`, of which no case is
proved anywhere below, and it says nothing at an affine place.  It is one coefficient, at one point.

⚠️ Earlier wording said `[2]` "genuinely ramifies at the `2`-torsion points" when `char F ≠ 2`.
That is **false**: `EllipticCurves.FunctionField.MulByTwoFibreInfinity` (`#774`) computes the index
`1` at every affine `2`-torsion point over an algebraically closed base field, and identifies what
does ramify there as `x ∘ [2] : ℙ¹ → ℙ¹` rather than `[2] : E → E`.

## Relation to `divisorProj_mulByTwoEndo_apply_none`

`MulByTwoPlaceAtInfinity` already carries
`divisorProj_mulByTwoEndo_apply_none : divisorProj W (f ∘ [2]) none = divisorProj W f none`, which
looks like the same statement.  They are not duplicates, and the primitive one is neither:

* the primitive facts are the two computations `comapProjPointTwo_none` and
  `ramificationIdxTwo_none`, and both statements are one `rw` from them;
* `divisorProj_mulByTwoEndo_apply_none` is about divisors **of functions**, and is proved from the
  pointwise transport in `PlacePullback` — it does not need this file's `pullbackDivisor` at all;
* `pullbackDivisorTwo_apply_none` is about an **arbitrary** divisor `D : ProjPoint W →₀ ℤ`, whether
  or not it is `div f` of anything, and is therefore strictly more general.

The `example` below derives the former from the latter through `divisorProj_mulByTwoEndo`, which is
the honest statement of how they are related: the function-level lemma is the specialisation
`D = div f`.

## A note on `simp`

`pullbackDivisorTwo_apply_none` is deliberately **not** tagged `@[simp]`.  The general
`pullbackDivisorTwo_apply` already is, and its left-hand side also matches at `p = none`; since
`comapProjPointTwo_none` and `ramificationIdxTwo_none` are not themselves simp lemmas, a `simp`
call that fires the general one first leaves the goal in the abstract form.  Checked, not guessed:
replacing the proof below by `simp` fails with

```
⊢ ramificationIdxTwo h2 none * D (comapProjPointTwo h2 none) = D none
```

Rewriting with this lemma explicitly is unambiguous, and that is what a consumer should do.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.3, III.4.
-/

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]

/-- **`[2]∗` fixes the coefficient at infinity of every divisor.**  Because `[2]` fixes the point at
infinity (`comapProjPointTwo_none`) and is unramified there (`ramificationIdxTwo_none`), the
coefficient of `pullbackDivisorTwo h2 D` at `none` is the coefficient of `D` at `none` — no
multiplication by an index and no change of point.

This is the first coefficient of a pulled-back divisor computed in this tree.  It says nothing at
an affine place — but ⚠️ not because `[2]` ramifies there, which earlier wording claimed and which
is false (`EllipticCurves.FunctionField.MulByTwoFibreInfinity`, `#774`). -/
theorem pullbackDivisorTwo_apply_none (h2 : (2 : F) ≠ 0) (D : ProjPoint W →₀ ℤ) :
    pullbackDivisorTwo h2 D (none : ProjPoint W) = D none := by
  rw [pullbackDivisorTwo_apply, comapProjPointTwo_none h2, ramificationIdxTwo_none h2, one_mul]

/-- `MulByTwoPlaceAtInfinity`'s `divisorProj_mulByTwoEndo_apply_none` is the specialisation of
`pullbackDivisorTwo_apply_none` to `D = div f`, through the merged functoriality
`divisorProj_mulByTwoEndo`.  Recorded as an `example` rather than a second declaration: the
statement is already in the tree, and what is worth committing is the derivation. -/
example (h2 : (2 : F) ≠ 0) {f : W.FunctionField} (hf : f ≠ 0) :
    divisorProj W (mulByTwoEndo h2 f) (none : ProjPoint W) = divisorProj W f none := by
  rw [divisorProj_mulByTwoEndo h2 hf, pullbackDivisorTwo_apply_none]

/-! ### Non-vacuity

`pullbackDivisorTwo` carries `[IsDedekindDomain W.CoordinateRing]` and is built from a choice
principle, so the statement above is worth instantiating on a curve where every instance is
discharged. -/

section Nonvacuity

/-- The curve `y² = x³ - x` over `ℚ`, of discriminant `64`. -/
private def exampleCurve : Affine ℚ := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

example : IsDedekindDomain exampleCurve.CoordinateRing := inferInstance

example (D : ProjPoint exampleCurve →₀ ℤ) :
    pullbackDivisorTwo (W := exampleCurve) (by norm_num) D (none : ProjPoint exampleCurve)
      = D none :=
  pullbackDivisorTwo_apply_none _ D

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
