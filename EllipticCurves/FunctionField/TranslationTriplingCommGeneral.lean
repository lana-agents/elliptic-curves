/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.MulByThreeFinite
import EllipticCurves.FunctionField.TranslationDoublingCommGeneral
import EllipticCurves.FunctionField.TranslationTriplingComm

/-!
# The general tripling/translation commutation `τ_P∗ ∘ [3]∗ = [3]∗ ∘ τ_T∗` for `[3]P = T`

`EllipticCurves.FunctionField.TranslationTriplingComm` proves the commutation of `translateEndo`
with `mulByThreeEndo` **only** in the degenerate case: for a `3`-torsion `T`,
`translateEndo hT (mulByThreeEndo h2 h3 f) = mulByThreeEndo h2 h3 f`.  Read geometrically that is
`[3](Q + T) = [3]Q`, i.e. `[3]T = O`, and it is the case `P := T` of the identity below with the
right-hand translation collapsing to the identity.

This file proves the **general** form.  For affine points `P` and `T` with `[3]P = T`,

```
[3](Q + P) = [3]Q + T        ⟹        τ_P∗ ([3]∗ f) = [3]∗ (τ_T∗ f).
```

⚠️ **The two translations are on opposite sides and by different points.**  With `τ_P∗ f = f ∘ τ_P`
and `[3]∗ f = f ∘ [3]`,

```
(τ_P∗ ([3]∗ f))(Q) = f(3(Q + P)) = f(3Q + T) = (τ_T∗ f)(3Q) = ([3]∗ (τ_T∗ f))(Q),
```

so it is `translateEndo hP ∘ mulByThreeEndo = mulByThreeEndo ∘ translateEndo hT`.  Writing it the
other way round gives a false statement.

## Main results

* `translateEndoAlgHom_comp_mulByThreeEndoAlgHom` — the identity as `F`-algebra endomorphisms;
* `translateEndo_mulByThreeEndo_comp_general` — as ring homomorphisms;
* `translateEndo_mulByThreeEndo_apply_general` — its applied form;
* `translateEndo_mulByThreeEndo_apply_of_baseField` — the same, from the **base-field** relation
  `P ⊕ P ⊕ P = T` in `W.Point`, which is the shape a caller actually has: the assembly gets `P`
  from `nsmul_three_surjective` (`Torsion/TriplingSurjective`, `#690`).

`mulByThreeEndoAlgHom` — `[3]∗` as an `F`-algebra endomorphism of `F(W)`, which is what
`genPointHom` consumes — is new, and lives in `MulByThreeFinite` beside its own `commutes'` field,
the placement `#699` chose for `mulByTwoEndoAlgHom`.

## Did the `n = 2` API generalise?  Yes, unchanged

`TranslationDoublingCommGeneral`'s docstring claims its supporting API is "reusable for `[3]` and
for any other `F`-algebra endomorphism of `F(W)`".  That claim is **correct as stated**: this file
reuses `algHom_ext_gen`, `nonsingular_algHom`, `genPointHom`, `genPointHom_some`,
`genPointHom_comp`, `algHom_ext_of_genPointHom`, `genPointHom_genericPoint_translate` and
`genPointHom_translatePoint` verbatim, with **no rework of any of them** and nothing added to that
file.  Only two things are `[3]`-specific:

* `mulByThreeEndoAlgHom`, a five-line near-copy of `mulByTwoEndoAlgHom`;
* `genPointHom_genericPoint_mulByThree`, one line, `(genericPoint_add_add_self h2 h3).symm`.

The group step is the only place where `n` is visibly present.  At `n = 2` it is
`add_add_add_comm`; here it is `(𝒫 + 𝒫_P) + (𝒫 + 𝒫_P) + (𝒫 + 𝒫_P) = (𝒫 + 𝒫 + 𝒫) + (𝒫_P + 𝒫_P + 𝒫_P)`
and `abel` discharges it — the issue's worry that `abel` might not fire on `(W ⁄ F(W)).Point` was
unfounded; Mathlib's `Point.instAddCommGroup` is enough and no `AddCommGroup` shim was needed.

**Consequence for general `n`, and it has been carried out.** The route is non-speculative in its
group-theoretic half: the same three lines prove `τ_P∗ ∘ [n]∗ = [n]∗ ∘ τ_T∗` for any `n`, with
`abel` handling the `n`-fold rearrangement.

⚠️ **The clause this paragraph used to carry has been paid** — it read *"What does not yet exist
for general `n` is the input the route consumes: `mulByNEndo` and the correspondence
`𝒫 + ⋯ + 𝒫 = (mulByNEndo genX, mulByNEndo genY)` are built separately at `n = 2`
(`GenericDoubling`) and `n = 3` (`GenericTripling`) out of the explicit addition formulæ, and a
uniform `n` needs the coordinate formula `#251`.  So general `n` is gated on `#251`, not on this
file's technique."*  Both named inputs are `EllipticCurves.FunctionField.MulByNPullback`'s at
every `n` — `mulByNEndo` and `nsmul_genericPoint_eq` — built from the **group law**, so the `ωₙ`
gating was never real.  The theorem those inputs were wanted for is
`translateEndo_mulByNEndo_apply_general` and its siblings in
`EllipticCurves.FunctionField.TranslationMulByNCommGeneral`, proved along exactly this route.
⚠️ *It is not attempted here* — that clause is file-scoped and stays true; this file remains the
`n = 3` slice.

⚠️ **`#404` is closed, and the general-`n` entry above named it as the gate.**  PR #557 proved the
on-curve identity for `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` at every index over every commutative ring —
`WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero`, `EllipticCurves.Torsion.OmegaCrux`.  What still
gates a general index is the *other* statement this tree also called `ωₙ`: the identification of
those coordinates with the **group-law** multiple `n • P`, which is `#251`.  ⚠️ The two-reading
account is `EllipticCurves.FunctionField.MulByNPullback`; the gate is relettered here, not lifted.

## What is *not* here

* Step B at `n = 3` — the divisor telescoping `f_T · (τ_T∗ f_T) · (τ_{−T}∗ f_T)`, which landed
  separately as `WeilPairingTelescopeThree` (`#712`) and is not imported here.
* The assembly `e_3(T, T) = 1`, `#418`, antisymmetry, Ward.
* Any rewriting of `TranslationTriplingComm` in terms of the group route.  Whether its ~250 lines
  of coordinate work are now redundant is a `#699`-style de-duplication question and belongs in its
  own issue; note that its statement is *not* literally the `P := T` case of the theorems below,
  since it concludes `translateEndo hT (mulByThreeEndo h2 h3 f) = mulByThreeEndo h2 h3 f`, which
  needs the extra step `translateEndo hO = id` — the point at infinity is not an affine `T`.
* Any generalisation of `translateEndo` to a non-rational or possibly-zero translation point
  (`#679`, `#689`): both `P` and `T` here are affine `F`-points, given by `W.Equation`.

## Characteristic hypotheses

`(2 : F) ≠ 0` and `(3 : F) ≠ 0`, inherited from `mulByThreeEndo`, whose construction goes through
the generic-point tripling formula.  (`#690` dropped its own `(3 : F) ≠ 0`, but that was about
`deg Ψ₃ = 4` in a division-polynomial argument and does not apply here.)

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.
-/

open Polynomial

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic] {xP yP xT yT : F}

/-- `[3]∗` acts on the generic point as the group triple — the merged `genericPoint_add_add_self`,
read through `genPointHom`. -/
lemma genPointHom_genericPoint_mulByThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    genPointHom (mulByThreeEndoAlgHom (W := W) h2 h3) genericPoint
      = genericPoint + genericPoint + genericPoint :=
  (genericPoint_add_add_self h2 h3).symm

/-! ### The commutation -/

/-- **The commutation, as `F`-algebra endomorphisms.**  For affine points `P`, `T` with `[3]P = T`
in `(W ⁄ F(W)).Point`,

```
τ_P∗ ∘ [3]∗ = [3]∗ ∘ τ_T∗.
```

The proof is the group calculation `(𝒫 + 𝒫_P) + (𝒫 + 𝒫_P) + (𝒫 + 𝒫_P) = (𝒫 + 𝒫 + 𝒫) + 𝒯`
transported through `genPointHom`; see the module docstring. -/
theorem translateEndoAlgHom_comp_mulByThreeEndoAlgHom (hP : W.Equation xP yP)
    (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (htriple : translatePoint hP + translatePoint hP + translatePoint hP = translatePoint hT) :
    (translateEndoAlgHom hP).comp (mulByThreeEndoAlgHom h2 h3)
      = (mulByThreeEndoAlgHom h2 h3).comp (translateEndoAlgHom hT) := by
  refine algHom_ext_of_genPointHom ?_
  simp only [← genPointHom_comp, genPointHom_genericPoint_mulByThree,
    genPointHom_genericPoint_translate, map_add, genPointHom_translatePoint]
  rw [← htriple]
  abel

/-- **The commutation, as ring homomorphisms.**  `(translateEndo hP).comp (mulByThreeEndo h2 h3)
= (mulByThreeEndo h2 h3).comp (translateEndo hT)` whenever `[3]P = T`.

The merged `translateEndo_mulByThreeEndo_comp` is *not* this statement: it is the degenerate case
`P := T` with `[3]T = O`, where the right-hand side collapses to `mulByThreeEndo h2 h3`. -/
theorem translateEndo_mulByThreeEndo_comp_general (hP : W.Equation xP yP)
    (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (htriple : translatePoint hP + translatePoint hP + translatePoint hP = translatePoint hT) :
    (translateEndo hP).comp (mulByThreeEndo h2 h3)
      = (mulByThreeEndo h2 h3).comp (translateEndo hT) :=
  congrArg AlgHom.toRingHom (translateEndoAlgHom_comp_mulByThreeEndoAlgHom hP hT h2 h3 htriple)

/-- **The commutation in applied form.**  For every `f : F(W)`,
`τ_P∗ ([3]∗ f) = [3]∗ (τ_T∗ f)` when `[3]P = T`. -/
theorem translateEndo_mulByThreeEndo_apply_general (hP : W.Equation xP yP)
    (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (htriple : translatePoint hP + translatePoint hP + translatePoint hP = translatePoint hT)
    (f : W.FunctionField) :
    translateEndo hP (mulByThreeEndo h2 h3 f) = mulByThreeEndo h2 h3 (translateEndo hT f) := by
  have h := translateEndo_mulByThreeEndo_comp_general hP hT h2 h3 htriple
  exact congr($h f)

open Classical in
/-- **The commutation from a base-field relation.**  The hypothesis a caller actually has is
`P ⊕ P ⊕ P = T` in `W.Point` — that is what `nsmul_three_surjective` produces — and the merged
`translatePoint_add` transports it to the `F(W)`-level relation the theorem above consumes. -/
theorem translateEndo_mulByThreeEndo_apply_of_baseField (hP : W.Equation xP yP)
    (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (htriple : torsionPoint hP + torsionPoint hP + torsionPoint hP = torsionPoint hT)
    (f : W.FunctionField) :
    translateEndo hP (mulByThreeEndo h2 h3 f) = mulByThreeEndo h2 h3 (translateEndo hT f) := by
  refine translateEndo_mulByThreeEndo_apply_general hP hT h2 h3 ?_ f
  -- `P ⊕ P ⊕ P = T` is `(P ⊕ P) ⊕ P = T`; `translatePoint_add` transports one `⊕` at a time, so
  -- the intermediate point `P ⊕ P` has to be named.  It is affine, because it is `T ⊖ P` and both
  -- of those are affine — but rather than produce its coordinates, transport the *pair* of
  -- relations through the group homomorphism directly.
  rw [← torsionPointMap_torsionPoint hP, ← torsionPointMap_torsionPoint hT, ← map_add, ← map_add,
    htriple]

/-! ### Non-vacuity

As in the `n = 2` case, the hypothesis `[3]P = T` with **both** `P` and `T` affine is genuinely
restrictive, and on the curves the rest of this subtree uses for certificates it can fail.  The
certificate here is again on `y² = x³ + 1` over `ℚ`, where `P = (2, 3)` has order `6`: it doubles
to `(0, 1)` and triples to the `2`-torsion point `T = (-1, 0)`, both affine. -/

section Nonvacuity

/-! The certificate curve `y² = x³ + 1` is the shared `EllipticCurves.Fixture.y2EqX3AddOne`, whose
single `[CharZero F]` instance also supplies `IsElliptic` here. -/

open EllipticCurves.Fixture

/-- `P = (2, 3)` lies on `y² = x³ + 1`. -/
private lemma exampleEqP : (y2EqX3AddOne ℚ).Equation 2 3 := by
  norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff]

/-- `2P = (0, 1)` lies on `y² = x³ + 1`. -/
private lemma exampleEqTwoP : (y2EqX3AddOne ℚ).Equation 0 1 := by
  norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff]

/-- `T = 3P = (-1, 0)` lies on `y² = x³ + 1`. -/
private lemma exampleEqT : (y2EqX3AddOne ℚ).Equation (-1) 0 := by
  norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff]

open Classical in
/-- `[3](2, 3) = (-1, 0)`: the tangent at `P` has slope `2`, giving `2P = (0, 1)`; the secant
through `(0, 1)` and `(2, 3)` has slope `1`, giving `3P = (-1, 0)`. -/
private lemma exampleTriple :
    torsionPoint exampleEqP + torsionPoint exampleEqP + torsionPoint exampleEqP
      = torsionPoint exampleEqT := by
  have hy : (3 : ℚ) ≠ (y2EqX3AddOne ℚ).negY 2 3 := by
    norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.negY]
  have hdouble : Point.some (2 : ℚ) 3
        ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEqP)
      + Point.some (2 : ℚ) 3 ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEqP)
      = Point.some (0 : ℚ) 1
        ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEqTwoP) := by
    rw [Point.add_self_of_Y_ne hy, Point.some.injEq]
    constructor <;>
      norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
        WeierstrassCurve.Affine.slope]
  have hx : (0 : ℚ) ≠ 2 := by norm_num
  have hsecant : Point.some (0 : ℚ) 1
        ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEqTwoP)
      + Point.some (2 : ℚ) 3 ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEqP)
      = Point.some (-1 : ℚ) 0
        ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEqT) := by
    rw [Point.add_of_X_ne hx, Point.some.injEq]
    constructor <;>
      norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
        WeierstrassCurve.Affine.slope]
  change Point.some (2 : ℚ) 3 _ + Point.some (2 : ℚ) 3 _ + Point.some (2 : ℚ) 3 _
    = Point.some (-1 : ℚ) 0 _
  rw [hdouble, hsecant]

-- The `convert` is bookkeeping, not mathematics: `translateEndo_mulByThreeEndo_apply_of_baseField`
-- is stated `open Classical in`, so the `+` in its hypothesis carries `Classical.propDecidable`,
-- while `exampleTriple` — elaborated at `F = ℚ`, where a `DecidableEq` instance exists — carries
-- `instDecidableEqRat`.  `convert ... using 5` closes the gap by `Subsingleton.elim` on the two
-- `DecidableEq ℚ` instances.  (The `n = 2` file needs `using 4`; the extra layer here is the third
-- summand.)
open Classical in
example (f : (y2EqX3AddOne ℚ).FunctionField) :
    translateEndo exampleEqP
        (mulByThreeEndo (W := y2EqX3AddOne ℚ) (by norm_num) (by norm_num) f)
      = mulByThreeEndo (by norm_num) (by norm_num) (translateEndo exampleEqT f) :=
  translateEndo_mulByThreeEndo_apply_of_baseField exampleEqP exampleEqT
    (by norm_num) (by norm_num) (by convert exampleTriple using 5) f

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
