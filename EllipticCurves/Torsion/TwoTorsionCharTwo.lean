/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.TwoTorsion
import Mathlib.Algebra.Field.ZMod

/-!
# `#E[2] ≤ 2` in characteristic `2`, so the `2`-descent route is not undecided there — it is false

`EllipticCurves.Torsion.TwoTorsion` computes `#E[2] = 4` over an algebraically closed field with
`(2 : F) ≠ 0`, and the whole halving tower above it — `HalvingExtension`, `HalvingGaloisTower`,
`TwoTorsionSplittingField` — carries that hypothesis forward.  ⚠️ **Each of those modules records
the absence separately and each SCOPES it to itself**, so none of them states it for the others.
`EllipticCurves.Torsion.HalvingExtension`'s is

> **Characteristic `2`.**  `halvingX` divides by `2` and is junk there; every statement that uses it
> non-trivially carries `(2 : F) ≠ 0`.  Nothing below decides whether a halving extension is
> separable in characteristic `2`.

— where *"Nothing below"* is that file and nothing else; `EllipticCurves.Torsion.HalvingGaloisTower`
inherits only the *hypothesis* (*"inherited from `HalvingExtension`"*) and writes its own clause,
and `EllipticCurves.Torsion.TwoTorsionSplittingField` writes a third.  ⚠️ **Four
independently-scoped clauses is a better argument for one theorem than one clause with reach would
be**, and all four now point here.

⚠️ **This file decides it, and the answer is that the question does not arise.**  In characteristic
`2` the count `#E[2] = 4` that the tower rests on is not merely unproved, it is **false**: `E[2]`
has at most **two** elements over *any* field of characteristic `2`, algebraically closed or not.

## The mechanism, and it is two lines

A point is `2`-torsion exactly when it is its own negative, which for an affine `(x, y)` is
`2y + a₁x + a₃ = 0` (`mem_torsion_two_some_iff`).  ⚠️ **In characteristic `2` the `y` drops out of
that equation entirely** and it becomes the *linear* condition

```
a₁ · x + a₃ = 0 ,
```

which has at most one solution — and none at all when `a₁ = 0`, because `a₃ ≠ 0` is then forced by
`[W.IsElliptic]`.  The `y` above such an `x` is unique too: the equation's `a₁xy + a₃y` term is
`(a₁x + a₃)y = 0`, so `y² = x³ + a₂x² + a₄x + a₆`, and `y ↦ y²` is injective in characteristic `2`.
**One affine point at most, plus the point at infinity.**

The same collapse is visible in the `2`-division polynomial: `Ψ₂Sq_eval_eq_sq`'s right-hand side
`(2y + a₁x + a₃)²` becomes `(a₁x + a₃)²`, and the univariate cubic itself degenerates to

```
Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆ = a₁²X² + a₃² = (a₁X + a₃)²          (`Ψ₂Sq_eq_sq_of_char_two`)
```

⚠️ **A cubic that has become a square**, so both of the facts `TwoTorsion` spends on it — degree
`3` and three distinct roots over a closure — fail at once, in **both** branches.  ⚠️ **Separability
is the one property that does NOT fail in both, and it is decided here rather than asserted**
(`separable_Ψ₂Sq_iff_a₁_eq_zero_of_char_two`): the square is of a genuinely *linear* polynomial
only when `a₁ ≠ 0`, and there `Ψ₂Sq` is inseparable; when `a₁ = 0` it is the nonzero **constant**
`a₃²`, hence a unit of `F[X]`, hence **separable**.  ⚠️ **`Ψ₂Sq = ℓ²` does not imply inseparable**,
because `ℓ` degenerates to a constant on exactly the branch `[W.IsElliptic]` forces to be nonzero.
That is the same degeneracy as the `n = 2` halving quartic's
(`EllipticCurves.Torsion.HalvingExtension`), one level down.

## Main statements

**12** declarations: **8** public theorems, one `private instance` and **3** `private` certificates,
the last four all in the `ℤ/2` non-vacuity block.  ⚠️ `#print axioms` over all eight public
statements reaches **0** `sorryAx` and nothing outside `{propext, Classical.choice, Quot.sound}`,
and all eight return all three.

Every statement takes `(2 : F) = 0` as an explicit hypothesis rather than `[CharP F 2]`; see
`## On the spelling of the hypothesis` below.  ⚠️ **Every statement *but the first* carries
`{F : Type*} [Field F] {W : Affine F}`** — the first is over `[CommRing R]` and is stated in its own
section below.  ⚠️ **The instance census, read off `#check` and not off the `variable` lines**:
`[DecidableEq F]` reaches **five** of the eight and `[W.IsElliptic]` reaches **six**, four of those
from `section Torsion`'s `variable` line and the other two as explicit binders on
`a₃_ne_zero_of_a₁_eq_zero_of_char_two` and `separable_Ψ₂Sq_iff_a₁_eq_zero_of_char_two`.
⚠️ **Neither is a dead binder**: `omit [DecidableEq F] in` before any of the five is refused with
*"cannot omit referenced section variable"*, and `[W.IsElliptic]` is the whole content of the
supersingular input.  ⚠️ **Three bullets below carry an explicit absence flag, and the binder is
named on each**: `Ψ₂Sq_eq_sq_of_char_two` (*no `[W.IsElliptic]`, no `[IsAlgClosed F]` and no
`[Field]`*), `separable_Ψ₂Sq_iff_a₁_eq_zero_of_char_two` (*no `[DecidableEq F]`*) and
`a₁_mul_add_a₃_eq_zero_of_mem_torsion_two_of_char_two` (*no `[W.IsElliptic]`*).  ⚠️ **Of the eight
exactly ONE carries neither binder** — the first of those three, the only one stated over
`[CommRing R]`.

* `WeierstrassCurve.Affine.Ψ₂Sq_eq_sq_of_char_two` — `Ψ₂Sq = (C a₁ · X + C a₃)²`, ⚠️ **over an
  arbitrary `[CommRing R]` and not only over a field**, which is where Mathlib's `Ψ₂Sq` lives.
  ⚠️ **No `[W.IsElliptic]`, no `[IsAlgClosed F]` and no `[Field]`**: it is an identity between
  polynomials in the `a`-invariants and binds none of them.  The field form is a direct instance of
  it, so no `example` recovers it and no consumer sees a narrower statement.
* `WeierstrassCurve.Affine.a₃_ne_zero_of_a₁_eq_zero_of_char_two` — if `a₁ = 0` then `a₃ ≠ 0`, from
  `[W.IsElliptic]` alone.  The whole content is that `a₁ = a₃ = 0` forces `Δ = 0` in characteristic
  `2`; this is the supersingular branch's only input.
* `WeierstrassCurve.Affine.separable_Ψ₂Sq_iff_a₁_eq_zero_of_char_two` — ⚠️ **`Ψ₂Sq` is separable in
  characteristic `2` exactly when `a₁ = 0`**, so separability there is decided in **both**
  directions rather than in one.  This is what `EllipticCurves.Torsion.TwoTorsionSplittingField`'s
  *"Nothing below decides whether the `2`-torsion field is separable there, in either direction"*
  was waiting for, and ⚠️ **the answer is not the one-directional *"it degenerates, so it is
  inseparable"* that the shape `Ψ₂Sq = ℓ²` suggests**: on the supersingular branch `ℓ` is a nonzero
  constant and the square of a unit is separable.  ⚠️ **No `[DecidableEq F]`.**
* `WeierstrassCurve.Affine.a₁_mul_add_a₃_eq_zero_of_mem_torsion_two_of_char_two` — the linear
  condition above, the file's workhorse.  ⚠️ **No `[W.IsElliptic]`.**
* `WeierstrassCurve.Affine.eq_of_mem_torsion_two_of_char_two` — **any two nonzero `2`-torsion points
  are equal.**  This is the sharp statement; the two counts below are corollaries of it.
* `WeierstrassCurve.Affine.card_torsion_two_le_two_of_char_two` — `#E[2] ≤ 2`.
* `WeierstrassCurve.Affine.card_torsion_two_ne_four_of_char_two` — `#E[2] ≠ 4`, the form a reader of
  the absence bullets quoted above is looking for.
* `WeierstrassCurve.Affine.torsion_two_eq_bot_of_a₁_eq_zero_of_char_two` — when `a₁ = 0`, `E[2]` is
  **trivial**, not merely small.  ⚠️ This is exact rather than a bound, and it needs no
  **perfectness** hypothesis on `F`, which is what its `a₁ ≠ 0` sibling needs.

## ⚠️ What is *not* here

* **`#E[2] = 2` when `a₁ ≠ 0`.**  ⚠️ **It is FALSE over a general field of characteristic `2`, and
  the bound above is sharp for that reason.**  The argument produces *at most* one affine
  `2`-torsion point by showing its `x` and then its `y` are determined; it does not produce one,
  because the determined `y` is a square root of `x³ + a₂x² + a₄x + a₆` and that need not exist.
  Over `𝔽₂(t)` it need not.  **`#E[2] = 2` holds exactly when `F` is perfect** — over a perfect
  field of characteristic `2` the Frobenius is surjective and the root is there — and this file does
  not state the perfect-field form because nothing in this tree consumes it.  ⚠️ **The two branches
  are the classical ordinary (`a₁ ≠ 0`) and supersingular (`a₁ = 0`) cases, and only the
  supersingular one is exact without a hypothesis on `F`**; that asymmetry is why
  `torsion_two_eq_bot_of_a₁_eq_zero_of_char_two` is an equality and its sibling is a bound.
* **Any theory of the Frobenius, of separability of `[2]` as an isogeny, or of supersingularity.**
  The words *ordinary* and *supersingular* appear above only to name the two branches of one
  `a₁ = 0` case split.  Nothing below imports a theory to state a count.
* **The `n = 3` analogue in characteristic `3`.**  Same shape, different division polynomial, and it
  belongs beside the `n = 3` work rather than here.
* **A sweep PAST the four modules this theorem reaches.**  The four are swept in this commit; the
  rest of the axis is not, and the seed is published here with **both its ends and its flag**,
  because ⚠️ **a census of this axis moves when this commit lands, and the seed is case-sensitive
  while half the clauses it counts are not.**  ``grep -rn 'characteristic `2`' --include=*.lean``
  over `EllipticCurves/` returns **59** hits in **33** files at `ac800b3`, and **67** in **35**
  under `-i`.  ⚠️ **The figure this commit publishes as its own is the DELTA, because that is the
  one that does not rot: `+22` hits and `+2` files case-sensitive, `+24` and `+1` under `-i`** —
  a property of this commit's diff, measured against `ac800b3` and reproduced unchanged against a
  `main` four commits later which had itself drifted `+2` under `-i`.  ⚠️ **So the absolute upper
  end moves with `main` and the delta does not**: read the totals as `ac800b3` plus this commit,
  **81** in **35** and **91** in **36**, and re-derive them rather than quoting them.
  ⚠️ **The whole delta is this commit's own prose**: **19** case-sensitive hits in this file, one
  each in **three of the four** swept modules — `TwoTorsion` (8 → 9), `HalvingExtension` (4 → 5)
  and `HalvingGaloisTower` (0 → 1) — and two more capitalised ones here under `-i`.
  ⚠️ **The fourth swept module, `TwoTorsionSplittingField`, gains none — its inserted sentence
  carries no lowercase occurrence of the phrase — and of the three that do gain one only
  `HalvingGaloisTower` was without the phrase beforehand**, so the `0 → 1` and the `8 → 9` are
  not the same kind of row.  ⚠️ **The absence clauses are bullet HEADERS, hence capitalised,
  so the case-sensitive seed cannot see them**: at `ac800b3` the **8** capitalised-only hits sit in
  8 distinct files and **two of those appear in no lowercase hit at all** — `HalvingGaloisTower` and
  `ThreeDivisionField`.  **Use `[Cc]haracteristic`, or `-i`.**  The four modules this file decides
  are `TwoTorsion`, `TwoTorsionSplittingField`, `HalvingExtension` and `HalvingGaloisTower`,
  ⚠️ **the last of which the case-sensitive seed could not see at `ac800b3` and can as of this
  commit**, its pointer sentence being its first lowercase occurrence.  The `Omega*`, `TateModule`
  and `Fixtures` clauses are about `ω`-forms, `ℓ`-adic indices and fixture base rings, and
  `ThreeDivisionField`'s is *"Characteristic `2` or `3`"* about the `3`-torsion; ⚠️ **nothing below
  decides those, and a pointer that claimed otherwise would widen past the theorem it cites.**
  ⚠️ **`TwoTorsionHalvingSquare`'s `## What is *not* here` carries a fifth clause of the same shape
  with a capitalised bullet** — named here so the next round need not rediscover it, and
  deliberately not taken, being outside the four this theorem covers.
* **A general-index statement.**  `card_torsion_eq_sq` (`EllipticCurves.Torsion.StructureGeneral`)
  is the `#E[n] = n²` at every `n` with `(n : F) ≠ 0`; it is **not** in this file's import closure
  and is not needed, because `n = 2` is precisely the index at which its hypothesis fails here.

## On the spelling of the hypothesis

⚠️ **`(2 : F) = 0` and `[CharP F 2]` are not interchangeable in a binder**, and this file uses the
first throughout.  The reason is symmetry with what it contradicts: every statement it is about —
`card_torsion_two`, `card_torsion_two_of_splits`, `card_torsion_two_halvingGaloisField`,
`torsionTwoEquiv` — binds `(2 : F) ≠ 0` as an explicit hypothesis, so `(2 : F) = 0` is the literal
negation and a reader can put the two side by side.  `EllipticCurves.Torsion.XSupport` is the tree's
only `CharP` consumer (`finite_torsion_of_not_dvd_charP`, `finite_torsion_of_lt_charP`) and it
converts through `CharP.cast_eq_zero_iff`; the same conversion is available to any caller that holds
`[CharP F 2]` instead.

## Non-vacuity

`EllipticCurves.Fixture.y2AddYEqX3` at `R = ZMod 2` — `y² + y = x³`, the supersingular branch, with
`a₁ = 0` and `a₃ = 1`.

⚠️ **`EllipticCurves.Fixtures` serves no characteristic-`2` CERTIFICATE and says in terms why** —
*"The finite-field certificates are deliberately NOT served here, and there are FOUR of them … In
full, so that no sweep has to rediscover it"*.  ⚠️ **It does declare the CURVE**: the definition
instantiated above is `Fixtures`' own `y2AddYEqX3`, whose docstring names this base and this
gap in terms — *"Over `ZMod 2` the same equation is supersingular … that is the char-`2`
certificate described in the module docstring, and it is not served here"*.  ⚠️ **And three of
those four certificates are this curve over this base**:
`exampleCurveChar2` (`EllipticCurves.FunctionField.NegYGalois`), `exampleCurveTwo`
(`EllipticCurves.FunctionField.NegYInvolution`) and `exampleCurveNegYGalois`
(`EllipticCurves.FunctionField.NegYGaloisGroup`), all `⟨0,0,1,0,0⟩`, all proving `IsElliptic` by
`decide +kernel`; and `EllipticCurves.FunctionField.FunctionFieldGaloisDescent`'s `Nonvacuity`
section uses `y2AddYEqX3` over `ZMod 2` itself.  ⚠️ **So the reason a fourth certificate is supplied
here is NOT that there is none — it is that all four sites are `private` or `example`s and all four
live under `FunctionField/`, which is DOWNSTREAM of `Torsion/`.**  `Fixtures`' own rule that
*"`private` hides a NAME, not an INSTANCE"* reaches only downstream of the declaring module, which
is the wrong direction here, and an import edge that fixed it would invert the tree.  The instance
below is therefore built by the three precedents' own one-line recipe — `isElliptic_iff`,
`isUnit_iff_ne_zero`, `decide +kernel` — rather than by a hand `Δ` computation, and `Fixtures`'
*"a later sweep should not 'finish the job' by deleting them"* protects this fourth one too.
⚠️ **No `Fact (Nat.Prime 2)` is declared here**: Mathlib's global `Nat.fact_prime_two` is what
resolves, and `Field (ZMod 2)` synthesises from this file's two imports alone.

`Δ = −27 · b₆² = −27 = 1` in `ZMod 2`, which is the discriminant `NegYGalois` records for the same
curve.  The certificate is `#E[2] = 1` **exactly**, not a bound, and the `≠ 4` corollary is
instantiated beside it so that the statement this file exists to contradict is contradicted at a
concrete curve.

## ⚠️ One Mathlib import beyond `TwoTorsion`, and it is the non-vacuity's and not the theory's

`Mathlib.Algebra.Field.ZMod` is imported for **`Field (ZMod 2)`** alone.  ⚠️ **Nothing in the theory
above needs it** — every public statement is over an abstract `[Field F]` and would compile against
`EllipticCurves.Torsion.TwoTorsion` alone — and it is here because this tree has no
characteristic-`2` field to certify against otherwise.  **A reader pricing this file's closure
should subtract that edge from the mathematics and charge it to the certificate.**

## References

* [Silverman, *The arithmetic of elliptic curves*][silverman2009], III.2 (the description of `E[2]`
  by the `2`-division polynomial) and V.3 (the two characteristic-`p` branches of `E[p]`).
-/

open Polynomial

namespace WeierstrassCurve.Affine

/-! ### The `2`-division polynomial degenerates to a square

⚠️ **This one section is over `[CommRing R]`**, because `Ψ₂Sq` is and the identity below needs
nothing else; every later section is over `[Field F]`. -/

section CommRing

variable {R : Type*} [CommRing R] {W : Affine R}

/-- **`Ψ₂Sq = (a₁X + a₃)²` in characteristic `2`.**

`Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆` loses its cubic and linear terms outright, while `b₂ = a₁² + 4a₂`
and `b₆ = a₃² + 4a₆` lose their `4`s, leaving `a₁²X² + a₃²`.

⚠️ **This is the univariate shadow of `Ψ₂Sq_eval_eq_sq`**, whose right-hand side
`(2y + a₁x + a₃)²` collapses the same way at every point of `W`; the two say the same thing and the
pointwise one is what the torsion count below actually uses.

⚠️ **Nothing here is about fields.**  `Ψ₂Sq` is Mathlib's, stated over a `CommRing`, and the proof
is one `linear_combination` in the `a`-invariants, so the statement is too; the `[Field F]` form
every consumer below wants is a direct instance. -/
theorem Ψ₂Sq_eq_sq_of_char_two (h2 : (2 : R) = 0) :
    W.Ψ₂Sq = (C W.a₁ * X + C W.a₃) ^ 2 := by
  have h2' : (2 : R[X]) = 0 := by
    rw [← map_ofNat (C : R →+* R[X]) 2, h2, map_zero]
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    map_add, map_mul, map_ofNat, map_pow]
  linear_combination (2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) * h2'

end CommRing

variable {F : Type*} [Field F] {W : Affine F}

/-! ### An elliptic curve in characteristic `2` has `a₁ ≠ 0` or `a₃ ≠ 0` -/

/-- **In characteristic `2` an elliptic curve cannot have `a₁ = a₃ = 0`.**

With both vanishing and `2 = 0` the `b`-invariants collapse to `b₂ = b₄ = b₆ = 0`, so every term of
`Δ = −b₂²b₈ − 8b₄³ − 27b₆² + 9b₂b₄b₆` vanishes and `[W.IsElliptic]` is contradicted.

⚠️ This is the only input the supersingular branch needs, and it is the reason
`torsion_two_eq_bot_of_a₁_eq_zero_of_char_two` below is an equality rather than a bound. -/
theorem a₃_ne_zero_of_a₁_eq_zero_of_char_two [W.IsElliptic] (h2 : (2 : F) = 0)
    (h1 : W.a₁ = 0) : W.a₃ ≠ 0 := by
  intro h3
  refine (‹W.IsElliptic›.isUnit).ne_zero ?_
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, h1, h3]
  linear_combination (144 * W.a₂ * W.a₆ * W.a₄ + 8 * W.a₂ ^ 2 * W.a₄ ^ 2 - 32 * W.a₂ ^ 3 * W.a₆
    - 216 * W.a₆ ^ 2 - 32 * W.a₄ ^ 3) * h2

/-! ### Separability of `Ψ₂Sq`, decided in both directions -/

/-- **`Ψ₂Sq` is separable in characteristic `2` exactly when `a₁ = 0`.**

⚠️ **This is the row `EllipticCurves.Torsion.TwoTorsionSplittingField` left open *"in either
direction"*, and the answer goes DIFFERENT ways in the two branches** — which is why the shape
`Ψ₂Sq = (C a₁ · X + C a₃)²` alone does not settle it:

* `a₁ ≠ 0` — the square of a genuinely *linear* polynomial, and `ℓ * ℓ ∣ Ψ₂Sq` with `ℓ` a non-unit,
  so `isUnit_of_self_mul_dvd_separable` refuses separability.  **Inseparable.**
* `a₁ = 0` — then `Ψ₂Sq = C (a₃ ^ 2)` with `a₃ ≠ 0` by
  `a₃_ne_zero_of_a₁_eq_zero_of_char_two`, a **unit** of `F[X]`, and `separable_C` makes every unit
  separable.  **Separable**, degree `0`, with no root anywhere — which is the same fact as
  `torsion_two_eq_bot_of_a₁_eq_zero_of_char_two` read off the polynomial.

⚠️ **So *"`Ψ₂Sq` degenerates to a square, hence is inseparable"* is a false inference**, and the
trap is that the degenerate branch is the one where `ℓ` stops being linear.  ⚠️ **On the curve this
file certifies — `y² + y = x³` over `ZMod 2`, where `a₁ = 0` — `Ψ₂Sq = 1`, and separability is
`separable_one`.**

`[W.IsElliptic]` is necessary and is not decoration: at `a₁ = a₃ = 0` the polynomial is `0`, which
is not separable, so the right-to-left direction is false without it. -/
theorem separable_Ψ₂Sq_iff_a₁_eq_zero_of_char_two [W.IsElliptic] (h2 : (2 : F) = 0) :
    W.Ψ₂Sq.Separable ↔ W.a₁ = 0 := by
  rw [Ψ₂Sq_eq_sq_of_char_two h2]
  refine ⟨fun hsep => ?_, fun h1 => ?_⟩
  · by_contra h1
    have hu : IsUnit (C W.a₁ * X + C W.a₃) :=
      isUnit_of_self_mul_dvd_separable hsep (by rw [sq])
    have hdeg := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_linear h1] at hdeg
    exact one_ne_zero hdeg
  · have h3 := a₃_ne_zero_of_a₁_eq_zero_of_char_two (W := W) h2 h1
    rw [h1, map_zero, zero_mul, zero_add, ← C_pow]
    exact (separable_C _).mpr (pow_ne_zero 2 h3).isUnit

/-! ### `E[2]` has at most one nonzero point -/

section Torsion

variable [DecidableEq F]

/-- **`2`-torsion in characteristic `2` is a LINEAR condition on `x` alone.**

`mem_torsion_two_some_iff` reads `2y + a₁x + a₃ = 0`, and the `y` term is killed by the
characteristic.  ⚠️ **This is the whole degeneracy**: away from characteristic `2` the same equation
determines `y` from `x` and leaves `x` cut out by a cubic, which is how `#E[2] = 4` arises; here it
leaves `y` entirely free and cuts `x` out by a *linear* polynomial. -/
theorem a₁_mul_add_a₃_eq_zero_of_mem_torsion_two_of_char_two (h2 : (2 : F) = 0)
    {x y : F} {h : W.Nonsingular x y} (hP : Point.some x y h ∈ W.torsion 2) :
    W.a₁ * x + W.a₃ = 0 := by
  have := (mem_torsion_two_some_iff h).mp hP
  linear_combination this - y * h2

variable [W.IsElliptic]

/-- **Any two nonzero `2`-torsion points of a curve in characteristic `2` are equal.**

The sharp statement of this file; both counts below are corollaries.  Three steps, and the
characteristic is spent in all three:

* `a₁ ≠ 0`, because `a₁ = 0` would force `a₃ = 0` through the linear condition and then contradict
  `a₃_ne_zero_of_a₁_eq_zero_of_char_two`;
* `x = x'`, by cancelling `a₁` in `a₁x + a₃ = 0 = a₁x' + a₃`;
* `y = y'`, because the Weierstrass equation's `a₁xy + a₃y` term is `(a₁x + a₃)y = 0`, so
  `y² = y'²`, and then `(y − y')² = y² − 2yy' + y'² = 0`.

⚠️ **The last step is Frobenius injectivity written out** rather than invoked: no `CharP` instance
and no `frobenius` appears, only `2 = 0` in a `linear_combination`. -/
theorem eq_of_mem_torsion_two_of_char_two (h2 : (2 : F) = 0) {P Q : W.Point}
    (hP : P ∈ W.torsion 2) (hQ : Q ∈ W.torsion 2) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) : P = Q := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd (show (Point.zero : W.Point) = 0 from rfl) hP0
  rcases Q with _ | ⟨x', y', h'⟩
  · exact absurd (show (Point.zero : W.Point) = 0 from rfl) hQ0
  have e := a₁_mul_add_a₃_eq_zero_of_mem_torsion_two_of_char_two h2 hP
  have e' := a₁_mul_add_a₃_eq_zero_of_mem_torsion_two_of_char_two h2 hQ
  have ha₁ : W.a₁ ≠ 0 := by
    intro h0
    refine a₃_ne_zero_of_a₁_eq_zero_of_char_two (W := W) h2 h0 ?_
    rw [h0] at e; simpa using e
  have hxx : x = x' := mul_left_cancel₀ ha₁ (by linear_combination e - e')
  subst hxx
  have E := (equation_iff x y).mp h.left
  have E' := (equation_iff x y').mp h'.left
  have hy : y ^ 2 = y' ^ 2 := by linear_combination E - E' - (y - y') * e
  have hsub : (y - y') ^ 2 = 0 := by linear_combination hy + (y' ^ 2 - y * y') * h2
  have hyy : y = y' := sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsub)
  subst hyy
  rfl

/-- **`#E[2] ≤ 2` over any field of characteristic `2`**, algebraically closed or not.

`P ↦ decide (P = 0)` is injective on `E[2]` by `eq_of_mem_torsion_two_of_char_two`, and `Bool` has
two elements.  ⚠️ **The bound is sharp and is not an equality** — see the module docstring's
`## ⚠️ What is *not* here`: over a non-perfect field the one candidate affine point need not
exist. -/
theorem card_torsion_two_le_two_of_char_two (h2 : (2 : F) = 0) :
    Nat.card (W.torsion 2) ≤ 2 := by
  classical
  have hinj : Function.Injective fun P : W.torsion 2 => decide ((P : W.Point) = 0) := by
    rintro ⟨P, hP⟩ ⟨Q, hQ⟩ hPQ
    simp only [decide_eq_decide] at hPQ
    by_cases h0 : P = 0
    · exact Subtype.ext (h0.trans (hPQ.mp h0).symm)
    · exact Subtype.ext (eq_of_mem_torsion_two_of_char_two h2 hP hQ h0 fun hq => h0 (hPQ.mpr hq))
  calc Nat.card (W.torsion 2) ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
    _ = 2 := by simp

/-- **`#E[2] ≠ 4` in characteristic `2`.**

⚠️ **This is the statement the `(2 : F) ≠ 0` hypothesis of `card_torsion_two`
(`EllipticCurves.Torsion.TwoTorsion`) exists for**, and it says that the hypothesis is necessary
rather than inherited decoration.  Everything the halving tower builds — the splitting field of
`Ψ₂Sq`, the halving extension, its normal closure and the `#E[2] = 4` carried over it — rests on a
count that is false here. -/
theorem card_torsion_two_ne_four_of_char_two (h2 : (2 : F) = 0) :
    Nat.card (W.torsion 2) ≠ 4 := by
  intro h
  have := card_torsion_two_le_two_of_char_two (W := W) h2
  omega

/-- **`E[2]` is trivial when `a₁ = 0`**, in characteristic `2` — the supersingular branch, and the
one of the two that is exact over every field.

The linear condition reads `a₃ = 0` there, and `a₃_ne_zero_of_a₁_eq_zero_of_char_two` refuses it, so
no affine point is `2`-torsion at all. -/
theorem torsion_two_eq_bot_of_a₁_eq_zero_of_char_two (h2 : (2 : F) = 0) (h1 : W.a₁ = 0) :
    W.torsion 2 = ⊥ := by
  refine eq_bot_iff.mpr fun P hP => ?_
  rcases P with _ | ⟨x, y, h⟩
  · exact AddSubgroup.mem_bot.mpr rfl
  · exact absurd (by
      have e := a₁_mul_add_a₃_eq_zero_of_mem_torsion_two_of_char_two h2 hP
      rw [h1] at e; simpa using e) (a₃_ne_zero_of_a₁_eq_zero_of_char_two (W := W) h2 h1)

end Torsion

/-! ### Non-vacuity over `ZMod 2`

`y² + y = x³`, the supersingular branch.  ⚠️ **No `Fact (Nat.Prime 2)` is declared here** —
Mathlib's global `Nat.fact_prime_two` resolves it and `Field (ZMod 2)` synthesises from this file's
two imports alone.  The module docstring's `## Non-vacuity` says why a fourth
`⟨0,0,1,0,0⟩`-over-`ZMod 2` certificate is owed at all, given that the tree already has three. -/

section Nonvacuity

open EllipticCurves.Fixture

/-- `IsElliptic` for `y² + y = x³` over `ZMod 2`: `Δ = −27 · b₆² = −27 = 1`, and `1 ≠ 0` there.

⚠️ **This is the one-line recipe the tree's three other `⟨0,0,1,0,0⟩`-over-`ZMod 2` certificates
use**, which `EllipticCurves.Fixtures` records of all four of its finite-field rows (*"All four
prove `IsElliptic` by `decide +kernel`"*).  ⚠️ `EllipticCurves.Fixtures`' own instance for this
curve does not reach here — it is stated over a field where `−27 ≠ 0` is a `norm_num` fact, and
`ZMod 2` is not one by that route. -/
private instance : (y2AddYEqX3 (ZMod 2)).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  decide +kernel

/-- **`E[2]` is trivial on `y² + y = x³` over `ZMod 2`** — `a₁ = 0`, so the supersingular branch,
and the conclusion is an equality and not a bound. -/
private theorem exampleTorsionTwoBotCharTwo : (y2AddYEqX3 (ZMod 2)).torsion 2 = ⊥ :=
  torsion_two_eq_bot_of_a₁_eq_zero_of_char_two (by decide) (by decide)

/-- **`#E[2] = 1`** there, read off the triviality above. -/
private theorem exampleCardTorsionTwoCharTwo :
    Nat.card ((y2AddYEqX3 (ZMod 2)).torsion 2) = 1 := by
  rw [exampleTorsionTwoBotCharTwo]; simp

/-- **`#E[2] ≠ 4`** there — the statement this file exists to make, at a concrete curve. -/
private theorem exampleCardTorsionTwoNeFourCharTwo :
    Nat.card ((y2AddYEqX3 (ZMod 2)).torsion 2) ≠ 4 :=
  card_torsion_two_ne_four_of_char_two (by decide)

end Nonvacuity

end WeierstrassCurve.Affine
