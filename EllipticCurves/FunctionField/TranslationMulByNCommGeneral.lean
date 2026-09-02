/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.MulByNTranscendence
import EllipticCurves.FunctionField.TranslationTorsionMap
import EllipticCurves.FunctionField.TranslationTriplingCommGeneral

/-!
# The general commutation `τ_P∗ ∘ [n]∗ = [n]∗ ∘ τ_T∗` for `[n]P = T`, at every `n`

`EllipticCurves.FunctionField.TranslationDoublingCommGeneral` and
`EllipticCurves.FunctionField.TranslationTriplingCommGeneral` prove
`τ_P∗ ∘ [m]∗ = [m]∗ ∘ τ_T∗` at `m = 2` and `m = 3`.  This file proves it for every `n : ℕ`, for
affine points `P` and `T` with `[n]P = T`:

```
[n](Q + P) = [n]Q + T        ⟹        τ_P∗ ([n]∗ f) = [n]∗ (τ_T∗ f).
```

⚠️ **The two translations are on opposite sides and by different points.**  With `τ_P∗ f = f ∘ τ_P`
and `[n]∗ f = f ∘ [n]`,

```
(τ_P∗ ([n]∗ f))(Q) = f(n(Q + P)) = f(nQ + T) = (τ_T∗ f)(nQ) = ([n]∗ (τ_T∗ f))(Q),
```

so it is `translateEndo hP ∘ mulByNEndo = mulByNEndo ∘ translateEndo hT`.  Writing it the other way
round gives a false statement.

## Main results

* `translateEndoAlgHom_comp_mulByNEndoAlgHom` — the identity as `F`-algebra endomorphisms;
* `translateEndo_mulByNEndo_comp_general` — as ring homomorphisms;
* `translateEndo_mulByNEndo_apply_general` — its applied form;
* `translateEndo_mulByNEndo_apply_of_baseField` — the same, from the **base-field** relation
  `n • P = T` in `W.Point`;
* `translateEndoAlgHom_comp_mulByNEndoAlgHom_torsion`,
  `translateEndo_mulByNEndo_comp_torsion`, `translateEndo_mulByNEndo_apply_torsion` and
  `…_torsion_of_baseField` — **the torsion case** `τ_T∗ ∘ [n]∗ = [n]∗` for an `n`-torsion `T`,
  whose target point is `O` and which therefore is not an instance of the four above;
* `translateEndo_mulByNEndoOfAlgClosed_apply` — over `F̄` with `2 ≠ 0`, where the transcendence
  hypothesis is automatic for every `n ≠ 0`;
* `mulByNEndoAlgHom_two`, `mulByNEndoAlgHom_three` — the identification of `[n]∗` at `n = 2, 3`
  with the merged `mulByTwoEndoAlgHom` and `mulByThreeEndoAlgHom`, from which the two merged
  commutations are recovered below.

## Where the input came from, and what this file does *not* need

The route is the one `TranslationDoublingCommGeneral` set up and `TranslationTriplingCommGeneral`
reused unchanged: transport the identity through `genPointHom`, the action of an `F`-algebra
endomorphism of `F(W)` on `(W ⁄ F(W)).Point`.  This file cites `genPointHom`, `genPointHom_comp`,
`algHom_ext_of_genPointHom`, `genPointHom_genericPoint_translate` and `genPointHom_translatePoint`
directly, and `algHom_ext_gen`, `nonsingular_algHom` and `genPointHom_some` through them; nothing
in that file was reworked and nothing was added to it.

What was missing at general `n` was not the technique but its input: `[n]∗` itself, and the
correspondence `n • 𝒫 = (mulByNEndo n hn (genX W), mulByNEndo n hn (genY W))`.  Both are the merged
`mulByNEndo` and `nsmul_genericPoint_eq` of `MulByNPullback`, built from the **group law** on
`(W ⁄ F(W)).Point`.  In particular nothing here uses the `y`-coordinate division polynomial `ωₙ`,
the general `n` on-curve identity (`#404`, since closed) or the elliptic-net recurrence
(Ward, `#260`, since closed); the
coordinates of `[n]` as rational functions remain unavailable and are not needed.

⚠️ **Both of the things that sentence names are now closed, and it is an independence claim
rather than a gate.**  `#404`'s on-curve identity is
`WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero` (`EllipticCurves.Torsion.OmegaCrux`, PR #557, at
every index over every commutative ring) and Ward's theorem (`#260`) is
`WeierstrassCurve.Affine.ψ_isEllipticNet` (`EllipticCurves.Torsion.WardHalving`), unconditional.
The claim below is unchanged in force: this file uses neither.  ⚠️ What is still open in this
neighbourhood is `#251`, the identification of `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` with `n • P`; see
`EllipticCurves.FunctionField.MulByNPullback`.

Only two things are `n`-specific, mirroring the `n = 3` file's two:

* `mulByNEndoAlgHom`, whose `commutes'` field is the merged `mulByNEndo_algebraMap_base` and which
  therefore lives beside it in `MulByNPullback`, following the placement `#699` chose;
* `genPointHom_genericPoint_mulByN`, one line, `(nsmul_genericPoint_eq n hn).symm`.

**The group step is easier here than at `n = 2, 3`, not harder.**  At `n = 2` it is
`add_add_add_comm`; at `n = 3` it is `abel`.  At general `n` it is
`n • (𝒫 + 𝒫_P) = n • 𝒫 + n • 𝒫_P`, which is the single lemma `nsmul_add`; no rearrangement arises.

## The hypothesis, and what discharges it

Every statement below carries `hn : Transcendental F (n • 𝒫).xCoord` — geometrically, that `[n]` is
non-constant — exactly as `mulByNEndo` does.  Over an algebraically closed field of characteristic
`≠ 2` it is automatic for `n ≠ 0` (`transcendental_xCoord_nsmul_of_isAlgClosed`), which is the
corollary at the end; over a general field it follows from **one** base-field point that is not
`n`-torsion (`transcendental_xCoord_nsmul_genericPoint`), which is how the non-vacuity certificate
discharges it at `n = 4` over `ℚ`.

## What is *not* here

* **`[n]`-surjectivity on the base field.**  At `n = 2, 3` the caller obtained `P` from a
  surjectivity result (`nsmul_three_surjective`, `Torsion/TriplingSurjective`, `#690`); there is no
  general `n` counterpart on this tree, and producing one needs the place theory of `mulByNEndo`.
  So `translateEndo_mulByNEndo_apply_of_baseField` takes the relation `n • P = T` as a hypothesis
  and does not attempt to discharge it.  ⚠️ The **torsion** statements need none of this: their
  hypothesis is `n • T = 0`, which a member of `E[n]` carries by definition, so
  `translateEndo_mulByNEndo_apply_torsion_of_baseField` leaves nothing undischarged.
* **Any rewriting of `TranslationTriplingComm`'s ~250 lines of coordinate work.**  Whether they are
  now redundant is a `#699`-style de-duplication question and belongs in its own issue, as the
  `n = 3` file already recorded.
* **Any Weil-pairing assembly** — `#418`, antisymmetry, `hcomm` at general `n`.  This supplies one
  input, not a rung.
* **Any generalisation of `translateEndo` to a non-rational or possibly-zero translation point**
  (`#679`, `#689`): both `P` and `T` here are affine `F`-points, given by `W.Equation`.

## Characteristic hypotheses

None, at general `n`: `mulByNEndo` needs no `(2 : F) ≠ 0` or `(3 : F) ≠ 0`, because it does not go
through the explicit doubling or tripling formulæ.  The two hypotheses reappear only in the
recovery of the merged `n = 2, 3` statements, which are stated in terms of `mulByTwoEndo` and
`mulByThreeEndo`, and in the algebraically closed corollary, which needs `(2 : F) ≠ 0` for the
`2`-primary torsion it takes its non-torsion point from.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.
-/

open Polynomial

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic] {xP yP xT yT : F}

/-- `[n]∗` acts on the generic point as the group multiple — the merged `nsmul_genericPoint_eq`,
read through `genPointHom`. -/
lemma genPointHom_genericPoint_mulByN (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) :
    genPointHom (mulByNEndoAlgHom n hn) genericPoint = n • genericPoint (W := W) :=
  (nsmul_genericPoint_eq n hn).symm

/-! ### The commutation -/

/-- **The commutation, as `F`-algebra endomorphisms.**  For affine points `P`, `T` with `[n]P = T`
in `(W ⁄ F(W)).Point`,

```
τ_P∗ ∘ [n]∗ = [n]∗ ∘ τ_T∗.
```

The proof is the group calculation `n • (𝒫 + 𝒫_P) = n • 𝒫 + n • 𝒫_P = n • 𝒫 + 𝒯` transported
through `genPointHom`; see the module docstring. -/
theorem translateEndoAlgHom_comp_mulByNEndoAlgHom (hP : W.Equation xP yP) (hT : W.Equation xT yT)
    (n : ℕ) (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hmul : n • translatePoint hP = translatePoint hT) :
    (translateEndoAlgHom hP).comp (mulByNEndoAlgHom n hn)
      = (mulByNEndoAlgHom n hn).comp (translateEndoAlgHom hT) := by
  refine algHom_ext_of_genPointHom ?_
  simp only [← genPointHom_comp, genPointHom_genericPoint_mulByN,
    genPointHom_genericPoint_translate, map_add, map_nsmul, genPointHom_translatePoint]
  rw [← hmul, nsmul_add]

/-- **The commutation, as ring homomorphisms.**  `(translateEndo hP).comp (mulByNEndo n hn)
= (mulByNEndo n hn).comp (translateEndo hT)` whenever `[n]P = T`. -/
theorem translateEndo_mulByNEndo_comp_general (hP : W.Equation xP yP) (hT : W.Equation xT yT)
    (n : ℕ) (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hmul : n • translatePoint hP = translatePoint hT) :
    (translateEndo hP).comp (mulByNEndo n hn)
      = (mulByNEndo n hn).comp (translateEndo hT) :=
  congrArg AlgHom.toRingHom (translateEndoAlgHom_comp_mulByNEndoAlgHom hP hT n hn hmul)

/-- **The commutation in applied form.**  For every `f : F(W)`,
`τ_P∗ ([n]∗ f) = [n]∗ (τ_T∗ f)` when `[n]P = T`. -/
theorem translateEndo_mulByNEndo_apply_general (hP : W.Equation xP yP) (hT : W.Equation xT yT)
    (n : ℕ) (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hmul : n • translatePoint hP = translatePoint hT) (f : W.FunctionField) :
    translateEndo hP (mulByNEndo n hn f) = mulByNEndo n hn (translateEndo hT f) := by
  have h := translateEndo_mulByNEndo_comp_general hP hT n hn hmul
  exact congr($h f)

open Classical in
/-- **The commutation from a base-field relation.**  The hypothesis a caller actually has is
`n • P = T` in `W.Point`; the merged `torsionPointMap_torsionPoint` transports it to the
`F(W)`-level relation the theorem above consumes, through the base-change homomorphism
`torsionPointMap` commuting with `nsmul`.

⚠️ Unlike `n = 2, 3`, the relation is **not** discharged here: `[n]`-surjectivity on `E(F̄)` does
not exist on this tree.  See the module docstring. -/
theorem translateEndo_mulByNEndo_apply_of_baseField (hP : W.Equation xP yP) (hT : W.Equation xT yT)
    (n : ℕ) (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hmul : n • torsionPoint hP = torsionPoint hT) (f : W.FunctionField) :
    translateEndo hP (mulByNEndo n hn f) = mulByNEndo n hn (translateEndo hT f) := by
  refine translateEndo_mulByNEndo_apply_general hP hT n hn ?_ f
  rw [← torsionPointMap_torsionPoint hP, ← torsionPointMap_torsionPoint hT, ← map_nsmul, hmul]

/-! ### The torsion case: `[n] ∘ τ_T = [n]` when `T` is `n`-torsion

⚠️ The statements above take **two affine points** `P`, `T` with `[n]P = T`.  The case a translation
*action* of `E[n]` needs is `[n]T = O`, whose target point is the point at infinity — which is not
affine, so it cannot be substituted for `hT` above and is a separate statement rather than an
instance.  It is the general-`n` form of the merged `translateEndo_mulByTwoEndo_apply`
(`EllipticCurves.FunctionField.TranslationDoublingComm`) and
`translateEndo_mulByThreeEndo_apply` (`EllipticCurves.FunctionField.TranslationTriplingComm`), and
the proof is the one above with `add_zero` in place of the hypothesis. -/

/-- **The torsion commutation, as `F`-algebra endomorphisms.**  For an affine `n`-torsion point `T`
of `(W ⁄ F(W)).Point`,

```
τ_T∗ ∘ [n]∗ = [n]∗.
```

⚠️ Unlike the statements above there is **no second point**: the group calculation is
`n • (𝒫 + 𝒯) = n • 𝒫 + n • 𝒯 = n • 𝒫`, so the composite collapses rather than commuting past
another translation. -/
theorem translateEndoAlgHom_comp_mulByNEndoAlgHom_torsion (hT : W.Equation xT yT) (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (htors : n • translatePoint hT = 0) :
    (translateEndoAlgHom hT).comp (mulByNEndoAlgHom n hn) = mulByNEndoAlgHom n hn := by
  refine algHom_ext_of_genPointHom ?_
  simp only [← genPointHom_comp, genPointHom_genericPoint_mulByN,
    genPointHom_genericPoint_translate, map_nsmul]
  rw [nsmul_add, htors, add_zero]

/-- **The torsion commutation, as ring homomorphisms.**  `(translateEndo hT).comp (mulByNEndo n hn)
= mulByNEndo n hn` whenever `n • T = 0`. -/
theorem translateEndo_mulByNEndo_comp_torsion (hT : W.Equation xT yT) (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (htors : n • translatePoint hT = 0) :
    (translateEndo hT).comp (mulByNEndo n hn) = mulByNEndo n hn :=
  congrArg AlgHom.toRingHom (translateEndoAlgHom_comp_mulByNEndoAlgHom_torsion hT n hn htors)

/-- **The torsion commutation in applied form**, and the one a consumer holding an element of `E[n]`
uses: `τ_T∗ ([n]∗ f) = [n]∗ f` for every `f : F(W)`.

This is the shape `EllipticCurves.FunctionField.TranslationActionN` consumes to prove
`[n]∗F(W) ⊆ Fixed(E[n])`, and the exact general-`n` analogue of the datum
`EllipticCurves.FunctionField.TranslationActionThree` takes from
`translateEndo_mulByThreeEndo_apply`. -/
theorem translateEndo_mulByNEndo_apply_torsion (hT : W.Equation xT yT) (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (htors : n • translatePoint hT = 0) (f : W.FunctionField) :
    translateEndo hT (mulByNEndo n hn f) = mulByNEndo n hn f := by
  have h := translateEndo_mulByNEndo_comp_torsion hT n hn htors
  exact congr($h f)

open Classical in
/-- **The torsion commutation from a base-field relation.**  The hypothesis a caller actually has is
`n • T = 0` in `W.Point`; `translatePoint_nsmul_eq_zero`
(`EllipticCurves.FunctionField.TranslationTorsionMap`) is the uniform transport to the `F(W)`-level
relation, at every `n`.

⚠️ Unlike `translateEndo_mulByNEndo_apply_of_baseField`, nothing here is left undischarged: that
statement needs `[n]`-surjectivity on `E(F̄)` to produce its `P`, and this one needs no `P` at
all. -/
theorem translateEndo_mulByNEndo_apply_torsion_of_baseField (hT : W.Equation xT yT) (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (htors : n • torsionPoint hT = 0) (f : W.FunctionField) :
    translateEndo hT (mulByNEndo n hn f) = mulByNEndo n hn f :=
  translateEndo_mulByNEndo_apply_torsion hT n hn (translatePoint_nsmul_eq_zero hT htors) f

/-! ### Over an algebraically closed field -/

section IsAlgClosed

variable [IsAlgClosed F]

open Classical in
/-- **The commutation over `F̄`, for every `n ≠ 0`.**  The transcendence hypothesis is discharged by
the merged `transcendental_xCoord_nsmul_of_isAlgClosed`, so the only remaining input is the
relation `[n]P = T`. -/
theorem translateEndo_mulByNEndoOfAlgClosed_apply (hP : W.Equation xP yP) (hT : W.Equation xT yT)
    (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hmul : n • translatePoint hP = translatePoint hT) (f : W.FunctionField) :
    translateEndo hP (mulByNEndoOfAlgClosed h2 hn f)
      = mulByNEndoOfAlgClosed h2 hn (translateEndo hT f) :=
  translateEndo_mulByNEndo_apply_general hP hT n
    (transcendental_xCoord_nsmul_of_isAlgClosed h2 hn) hmul f

end IsAlgClosed

/-! ### Consistency with the merged `n = 2` and `n = 3` commutations

⚠️ This is the check that the route computes the **right** map, and it is the same check `#1165`
used to validate `mulByNEndo` itself: the general `[n]∗` is identified at `n = 2, 3` with the
endomorphisms built from the explicit doubling and tripling formulæ, and the two merged
commutations are then re-derived from the general one. -/

/-- **`[2]∗` built from the group law is the merged `mulByTwoEndoAlgHom`** — the `AlgHom` form of
the merged `mulByNEndo_two`. -/
theorem mulByNEndoAlgHom_two (h2 : (2 : F) ≠ 0) :
    mulByNEndoAlgHom 2 (transcendental_xCoord_two_nsmul (W := W) h2) = mulByTwoEndoAlgHom h2 :=
  AlgHom.coe_ringHom_injective (mulByNEndo_two h2)

/-- **`[3]∗` built from the group law is the merged `mulByThreeEndoAlgHom`** — the `AlgHom` form of
the merged `mulByNEndo_three`. -/
theorem mulByNEndoAlgHom_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    mulByNEndoAlgHom 3 (transcendental_xCoord_three_nsmul (W := W) h2 h3)
      = mulByThreeEndoAlgHom h2 h3 :=
  AlgHom.coe_ringHom_injective (mulByNEndo_three h2 h3)

/-- The merged `translateEndo_mulByTwoEndo_apply_general`, re-derived from the general `n` form at
`n = 2`.  Callers should keep using the merged name; this is a certificate, not new API. -/
example (hP : W.Equation xP yP) (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0)
    (hdouble : translatePoint hP + translatePoint hP = translatePoint hT) (f : W.FunctionField) :
    translateEndo hP (mulByTwoEndo h2 f) = mulByTwoEndo h2 (translateEndo hT f) := by
  have h := translateEndo_mulByNEndo_apply_general hP hT 2 (transcendental_xCoord_two_nsmul h2)
    (by rw [two_nsmul]; exact hdouble) f
  rwa [mulByNEndo_two] at h

/-- The merged `translateEndo_mulByThreeEndo_apply_general`, re-derived from the general `n` form at
`n = 3`.  Callers should keep using the merged name; this is a certificate, not new API. -/
example (hP : W.Equation xP yP) (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (htriple : translatePoint hP + translatePoint hP + translatePoint hP = translatePoint hT)
    (f : W.FunctionField) :
    translateEndo hP (mulByThreeEndo h2 h3 f) = mulByThreeEndo h2 h3 (translateEndo hT f) := by
  have h := translateEndo_mulByNEndo_apply_general hP hT 3
    (transcendental_xCoord_three_nsmul h2 h3)
    (by rw [three_nsmul, ← add_assoc]; exact htriple) f
  rwa [mulByNEndo_three] at h

/-! ### Non-vacuity

The hypothesis `[n]P = T` with **both** `P` and `T` affine is genuinely restrictive, so as at
`n = 2, 3` the theorems are certified on a curve where it holds.  The certificate is at `n = 4` —
the first index beyond the merged `2` and `3` — on `y² = x³ + 1` over `ℚ`, where `P = (2, 3)` has
order `6`, so `4P = -2P = (0, -1)` is affine.

⚠️ Over `ℚ` the transcendence hypothesis is *not* automatic, and the certificate has to discharge
it: `transcendental_xCoord_nsmul_genericPoint` needs one base-field point that is not `4`-torsion,
and `P` itself is one, since `4P = (0, -1) ≠ O`. -/

section Nonvacuity

/-! The certificate curve `y² = x³ + 1` is the shared `EllipticCurves.Fixture.y2EqX3AddOne`, whose
single `[CharZero F]` instance also supplies `IsElliptic` here. -/

open EllipticCurves.Fixture

/-- `P = (2, 3)` lies on `y² = x³ + 1`. -/
private lemma exampleEqPN : (y2EqX3AddOne ℚ).Equation 2 3 := by
  norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff]

/-- `2P = (0, 1)` lies on `y² = x³ + 1`. -/
private lemma exampleEqTwoPN : (y2EqX3AddOne ℚ).Equation 0 1 := by
  norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff]

/-- `3P = (-1, 0)` lies on `y² = x³ + 1`. -/
private lemma exampleEqThreePN : (y2EqX3AddOne ℚ).Equation (-1) 0 := by
  norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff]

/-- `T = 4P = (0, -1)` lies on `y² = x³ + 1`. -/
private lemma exampleEqTN : (y2EqX3AddOne ℚ).Equation 0 (-1) := by
  norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff]

open Classical in
/-- `[4](2, 3) = (0, -1)`: the tangent at `P` has slope `2`, giving `2P = (0, 1)`; the secant
through `(0, 1)` and `(2, 3)` has slope `1`, giving `3P = (-1, 0)`; the secant through `(-1, 0)`
and `(2, 3)` has slope `1`, giving `4P = (0, -1)`. -/
private lemma exampleQuadruple :
    (4 : ℕ) • torsionPoint exampleEqPN = torsionPoint exampleEqTN := by
  have hy : (3 : ℚ) ≠ (y2EqX3AddOne ℚ).negY 2 3 := by
    norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.negY]
  have hdouble : Point.some (2 : ℚ) 3
        ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEqPN)
      + Point.some (2 : ℚ) 3 ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEqPN)
      = Point.some (0 : ℚ) 1 ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEqTwoPN) := by
    rw [Point.add_self_of_Y_ne hy, Point.some.injEq]
    constructor <;>
      norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
        WeierstrassCurve.Affine.slope]
  have hx : (0 : ℚ) ≠ 2 := by norm_num
  have hsecant : Point.some (0 : ℚ) 1
        ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEqTwoPN)
      + Point.some (2 : ℚ) 3 ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEqPN)
      = Point.some (-1 : ℚ) 0 ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEqThreePN) := by
    rw [Point.add_of_X_ne hx, Point.some.injEq]
    constructor <;>
      norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
        WeierstrassCurve.Affine.slope]
  have hx' : (-1 : ℚ) ≠ 2 := by norm_num
  have hsecant' : Point.some (-1 : ℚ) 0
        ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEqThreePN)
      + Point.some (2 : ℚ) 3 ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEqPN)
      = Point.some (0 : ℚ) (-1) ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEqTN) := by
    rw [Point.add_of_X_ne hx', Point.some.injEq]
    constructor <;>
      norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
        WeierstrassCurve.Affine.slope]
  change (4 : ℕ) • Point.some (2 : ℚ) 3 _ = Point.some (0 : ℚ) (-1) _
  rw [show (4 : ℕ) = 3 + 1 from rfl, succ_nsmul, show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul,
    two_nsmul, hdouble, hsecant, hsecant']

open Classical in
/-- `P = (2, 3)` is not `4`-torsion, which is what discharges the transcendence hypothesis. -/
private lemma exampleNotFourTorsion : (4 : ℕ) • torsionPoint exampleEqPN ≠ 0 := by
  rw [exampleQuadruple, torsionPoint]
  exact fun h => by simp at h

-- The two `convert`s below are bookkeeping, not mathematics, and are the `nsmul` analogue of the
-- `convert ... using 4` / `using 5` the `n = 2` and `n = 3` certificates need.  The general
-- statements are elaborated `open Classical in` at an abstract `F`, so the `+` inside `n • ·` on
-- `W.Point` carries `Classical.propDecidable`; the certificates are elaborated at `F = ℚ`, where
-- `instDecidableEqRat` wins on priority.  `convert ... using 9` reaches
-- `Point.instAddCommGroup`'s own `DecidableEq` argument and closes the gap by `Subsingleton.elim`.
-- The depth is `9` rather than `4` because `n • x` goes through
-- `HSMul → SMul → NSMul → AddMonoid → SubNegMonoid → AddGroup → AddCommGroup`, where `x + x` goes
-- through `HAdd → Add` only; it is not a sign of anything harder happening.
open Classical in
/-- The transcendence hypothesis at `n = 4` over `ℚ`, discharged by `P` itself. -/
private lemma exampleTranscendentalFour :
    Transcendental ℚ ((4 : ℕ) • genericPoint (W := y2EqX3AddOne ℚ)).xCoord :=
  transcendental_xCoord_nsmul_genericPoint 4 (T := torsionPoint exampleEqPN)
    (by convert exampleNotFourTorsion using 9)

open Classical in
example (f : (y2EqX3AddOne ℚ).FunctionField) :
    translateEndo exampleEqPN (mulByNEndo 4 exampleTranscendentalFour f)
      = mulByNEndo 4 exampleTranscendentalFour (translateEndo exampleEqTN f) :=
  translateEndo_mulByNEndo_apply_of_baseField exampleEqPN exampleEqTN 4
    exampleTranscendentalFour (by convert exampleQuadruple using 9) f

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
