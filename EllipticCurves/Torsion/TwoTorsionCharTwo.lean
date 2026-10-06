/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.TwoTorsion
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.RatFunc.Basic

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

⚠️ **And the count is not left as a bound: it is DECIDED.**  `#E[2] = 1` when `a₁ = 0`, over every
field; and when `a₁ ≠ 0` it is `2` exactly when one element of `F` — the value of
`x³ + a₂x² + a₄x + a₆` at the single `x` with `a₁x + a₃ = 0` — is a square there, which
`card_torsion_two_eq_two_iff_of_a₁_ne_zero_of_char_two` states in both directions.  ⚠️ **So the two
values `E[2]` can take in characteristic `2` are `1` and `2`, the branch is read off `a₁`, and the
only thing that can be undecided is a square root and never the count.**  The headline above says
`≤ 2` because that is the inequality the halving tower's `#E[2] = 4` collides with; the equality is
the sharper fact and it is `card_torsion_two_of_sq_surjective_of_char_two`.

⚠️ **And the square root is not an artefact of the argument: it is exactly what perfectness of `F`
buys, over the whole family of curves at once.**  `#E[2] = 2` for **every** elliptic curve over `F`
with `a₁ ≠ 0` **iff** `F` is perfect (`perfectField_iff_forall_card_torsion_two_eq_two_of_char_two`)
— ⚠️ **both directions, over an arbitrary field, and the converse needs no imperfect field to state
or to prove**, because the curve that witnesses a missing square root of `c` is `⟨1, 0, 0, 0, c⟩`
over `F` itself, whose `Δ` **is** `c`.  ⚠️ **Read of a SINGLE curve the same words are false**, and
`y² + xy = x³ + 1` refutes them over every field of characteristic `2` at once.  The imperfect side
of the `↔` is not empty either: `y² + xy = x³ + t` over `𝔽₂(t)` has `a₁ ≠ 0` and `#E[2] = 1`, which
is the tree's first curve with that pair of properties.

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

**37** declarations: **21** public theorems, one `private def` (the ordinary family
`⟨1, 0, 0, 0, c⟩`), one anonymous `private instance` and **14** `private` theorems — the family's
`IsElliptic` lemma, the shared extraction engine
`sq_eq_of_mem_torsion_two_of_a₁_ne_zero_of_char_two`, and **12** certificates, the certificates
split over the three non-vacuity blocks as `3` (`ZMod 2`, supersingular), `4` (ordinary) and `5`
(`𝔽₂(t)`, imperfect).
⚠️ `#print axioms` over all twenty-one public statements reaches **0** `sorryAx` and nothing outside
`{propext, Classical.choice, Quot.sound}`, and all twenty-one return all three.

Every statement takes `(2 : F) = 0` as an explicit hypothesis rather than `[CharP F 2]`; see
`## On the spelling of the hypothesis` below.  ⚠️ **Exactly THREE of the twenty-one carry no
`{W : Affine F}` SECTION BINDER** — `perfectField_iff_sq_surjective_of_char_two`, which is about `F`
alone, and the two family statements, which bind their curve *inside* the statement
(`∀ W : Affine F, …`) because that quantifier is the point of them; every other one *but the first*
carries `{F : Type*} [Field F] {W : Affine F}`, the first being over `[CommRing R]` and stated in
its own section below.  ⚠️ **The binder count and the MENTION count come apart here and the second
is ONE**: `Affine F` occurs in both family statements' types, so a sentence saying *"three mention
no curve"* would be false of two of its own three, and it is the binder that is being counted.
⚠️ **The instance census, read off `#check` and not off the `variable` lines**:
`[DecidableEq F]` reaches **sixteen** of the twenty-one,
`[W.IsElliptic]` reaches **thirteen**, and `[PerfectField F]` reaches exactly **one** —
`card_torsion_two_of_perfectField_of_char_two`, still the only statement in the file with an
instance hypothesis on `F` beyond decidability, ⚠️ **and `PerfectField` now appears in two further
statements as a PROPOSITION rather than as a binder**, which is what
`perfectField_iff_sq_surjective_of_char_two` exists to make possible.
⚠️ **Neither of the first two is a dead binder**: `omit [DecidableEq F] in` before any of the
sixteen is refused with *"cannot omit referenced section variable"*, and `[W.IsElliptic]` is the
whole content of the supersingular input.  ⚠️ **Six bullets below carry an explicit absence flag,
and the binder is named on each**: `Ψ₂Sq_eq_sq_of_char_two` (*no `[W.IsElliptic]`, no
`[IsAlgClosed F]` and no `[Field]`*), `separable_Ψ₂Sq_iff_a₁_eq_zero_of_char_two`
(*no `[DecidableEq F]`*),
`a₁_mul_add_a₃_eq_zero_of_mem_torsion_two_of_char_two` (*no `[W.IsElliptic]`*),
`nonsingular_of_a₁_mul_add_a₃_eq_zero_of_sq_eq` (*no `(2 : F) = 0`*),
`torsion_two_eq_bot_of_a₁_ne_zero_of_not_sq_of_char_two` (*no `[W.IsElliptic]`*) and
`perfectField_iff_sq_surjective_of_char_two` (*no `[DecidableEq F]` and no curve*).  ⚠️ **Of the
twenty-one exactly TWO carry neither `[DecidableEq F]` nor `[W.IsElliptic]`** — the first and the
last of those six, and ⚠️ **the landed census said exactly ONE, which this round makes false rather
than finds false**: the second is the `PerfectField` bridge, which is not about a curve.
⚠️ **Exactly one still carries no characteristic hypothesis at all**, which is
`nonsingular_of_a₁_mul_add_a₃_eq_zero_of_sq_eq` and is the reason it has no `_of_char_two` suffix.

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
* `WeierstrassCurve.Affine.nonsingular_of_a₁_mul_add_a₃_eq_zero_of_sq_eq` — a square root of
  `x³ + a₂x² + a₄x + a₆` at an `x` with `a₁x + a₃ = 0` **is** the `y`-coordinate of a point.
  ⚠️ **No `(2 : F) = 0`**: the `y`-linear part of the Weierstrass equation is `(a₁x + a₃)y` and
  `hlin` kills it in every characteristic.  This is the half of the converse that can fail over a
  field the caller does not control, and the only half that can.
* `WeierstrassCurve.Affine.a₁_mul_add_a₃_eq_zero_of_mem_torsion_two_of_char_two` — the linear
  condition above, the file's workhorse.  ⚠️ **No `[W.IsElliptic]`.**
* `WeierstrassCurve.Affine.mem_torsion_two_some_of_a₁_mul_add_a₃_eq_zero_of_char_two` — the converse
  of the workhorse: in characteristic `2` a point whose `x` satisfies the linear condition **is**
  `2`-torsion, its `y` being unconstrained.  ⚠️ **No `[W.IsElliptic]`**, matching the forward
  direction.
* `WeierstrassCurve.Affine.mem_torsion_two_some_iff_a₁_mul_add_a₃_eq_zero_of_char_two` — the two
  packaged: `(x, y) ∈ E[2] ↔ a₁x + a₃ = 0`.  ⚠️ **The right-hand side does not mention `y`**, which
  is the whole degeneracy in one line.
* `WeierstrassCurve.Affine.eq_of_mem_torsion_two_of_char_two` — **any two nonzero `2`-torsion points
  are equal.**  This is the sharp statement; the two counts below are corollaries of it.
* `WeierstrassCurve.Affine.card_torsion_two_le_two_of_char_two` — `#E[2] ≤ 2`.
* `WeierstrassCurve.Affine.card_torsion_two_ne_four_of_char_two` — `#E[2] ≠ 4`, the form a reader of
  the absence bullets quoted above is looking for.
* `WeierstrassCurve.Affine.torsion_two_eq_bot_of_a₁_eq_zero_of_char_two` — when `a₁ = 0`, `E[2]` is
  **trivial**, not merely small.  ⚠️ This is exact rather than a bound, and it needs no
  hypothesis on `F` at all, which is what its `a₁ ≠ 0` sibling does need.
* `WeierstrassCurve.Affine.card_torsion_two_eq_two_of_ne_zero_of_char_two` — **one nonzero
  `2`-torsion point forces `#E[2] = 2`**.  This is where the `≤ 2` bound becomes an equality, and it
  asks nothing of `F`.
* `WeierstrassCurve.Affine.card_torsion_two_eq_two_iff_of_a₁_ne_zero_of_char_two` — ⚠️ **`#E[2] = 2`
  exactly when `x³ + a₂x² + a₄x + a₆` is a square at the one candidate `x`**, and ⚠️ **over an
  arbitrary field, with no perfectness and no finiteness.**  The sharp form of the whole ordinary
  branch: the obstruction is one square root, named, with both directions proved.
* `WeierstrassCurve.Affine.torsion_two_eq_bot_of_a₁_ne_zero_of_not_sq_of_char_two` — the negative
  half of the same dichotomy stated as an **equality**: no square root, no affine `2`-torsion point,
  `E[2] = ⊥`.  ⚠️ **No `[W.IsElliptic]`** — the forward workhorse is all it needs, and
  `[W.IsElliptic]` enters the `= 2` half only through the statement that BUILDS a point.
* `WeierstrassCurve.Affine.card_torsion_two_eq_one_iff_of_a₁_ne_zero_of_char_two` — ⚠️ **`#E[2] = 1`
  exactly when that element is NOT a square**, the complement of the `= 2` iff.  ⚠️ **The two
  together are what rule out `0`**, which `card_torsion_two_le_two_of_char_two` alone leaves open.
* `WeierstrassCurve.Affine.card_torsion_two_eq_two_of_a₁_ne_zero_of_char_two` — `#E[2] = 2` when
  squaring is onto `F`, the `x` being `a₃ / a₁`.
* `WeierstrassCurve.Affine.card_torsion_two_of_sq_surjective_of_char_two` — ⚠️ **the dichotomy:
  `#E[2] = 1` when `a₁ = 0` and `#E[2] = 2` when `a₁ ≠ 0`**, over any field whose squaring map is
  onto.  ⚠️ **Neither value is `4`**, and the branch the classical count would call generic is the
  one that gives `2`.
* `WeierstrassCurve.Affine.perfectField_iff_sq_surjective_of_char_two` — ⚠️ **`PerfectField F` ↔
  squaring is onto `F`**, in characteristic `2`, ⚠️ **and this one mentions no curve at all**.  The
  four-line `(2 : F) = 0 → CharP F 2` bridge that the dichotomy below used to carry inline lives
  here now, in **both** directions — ⚠️ **but every consumer in this file uses the FORWARD one**,
  and the declaration's own docstring says why the reverse half is stated anyway.
  ⚠️ **No `[DecidableEq F]`.**
* `WeierstrassCurve.Affine.card_torsion_two_of_perfectField_of_char_two` — the same dichotomy from
  `[PerfectField F]`.  ⚠️ **It is the form `## ⚠️ What is *not* here` used to declare absent**, and
  it is now three lines, the `CharP` conversion having moved to the bridge above.
* `WeierstrassCurve.Affine.sq_surjective_iff_forall_card_torsion_two_eq_two_of_char_two` —
  ⚠️ **squaring is onto `F` ↔ EVERY ordinary elliptic curve over `F` has `#E[2] = 2`.**  The
  quantifier is over curves and not over fields, so ⚠️ **the converse half needs no imperfect field
  to state and none to prove**: the witness is `⟨1, 0, 0, 0, c⟩`, one curve per element `c`, whose
  `Δ` **is** `c`.
* `WeierstrassCurve.Affine.perfectField_iff_forall_card_torsion_two_eq_two_of_char_two` —
  ⚠️ **the FAMILY reading of *"`#E[2] = 2` holds exactly when `F` is perfect"*, in both
  directions.**  This is the sentence `## ⚠️ What is *not* here` carried as half-absent; read of a
  single curve the same words are false, and the ordinary certificate below refutes them.

## ⚠️ What is *not* here

* **`#E[2] = 2` when `a₁ ≠ 0`, unconditionally on `F`.**  ⚠️ **It is FALSE over a general field of
  characteristic `2`**, and `card_torsion_two_eq_two_iff_of_a₁_ne_zero_of_char_two` now says exactly
  how: the argument produces *at most* one affine `2`-torsion point by showing its `x` and then its
  `y` are determined, and whether it produces one is whether the determined `y` — a square root
  of `x³ + a₂x² + a₄x + a₆` at the single `x` with `a₁x + a₃ = 0` — exists in `F`.  ⚠️ **Over
  `𝔽₂(t)` with `a₆ = t` it does not, and that is now a CERTIFICATE in this file and not an
  assertion** (`### ⚠️ The imperfect witness`).  ⚠️ **So the obstruction is one square root of one
  element, both halves of the dichotomy are theorems here, and both are witnessed.**
* ⚠️ **The SINGLE-CURVE reading of *"`#E[2] = 2` holds exactly when `F` is perfect"*, which is
  FALSE and stays out.**  `exampleCardTorsionTwoOrdinaryOfCharTwo` refutes it: `y² + xy = x³ + 1`
  has `#E[2] = 2` over **every** field of characteristic `2`, imperfect ones included, because its
  candidate `x` is `0` and the cubic's value there is `a₆ = 1 = 1²` — and `𝔽₂(t)`, which this file
  now certifies imperfect, is one of those fields.  ⚠️ **Perfectness is sufficient uniformly over
  curves and never necessary for a given curve** — that is the distinction the old sentence elided,
  and the asymmetry it went on to draw survives it:
  `torsion_two_eq_bot_of_a₁_eq_zero_of_char_two` is an equality over every field, while its
  `a₁ ≠ 0` sibling needs *something* — a square root, not necessarily perfectness.
  ⚠️ **The FAMILY reading of the same words is no longer absent**: it is
  `perfectField_iff_forall_card_torsion_two_eq_two_of_char_two`, in both directions, and the bullet
  that used to record its converse half as missing is the next one.
* ⚠️ **The REASON the converse half of the family reading was recorded as absent, which was
  wrong.**  This bullet used to say the converse *"needs an imperfect `F` and a curve witnessing
  the failure (`𝔽₂(t)`, `a₆ = t`)"*, and priced the `RatFunc` edge as the obstruction.
  ⚠️ **A statement universally quantified over curves does not need a field where it fails**: given
  `c : F` with no square root, `⟨1, 0, 0, 0, c⟩` is elliptic over `F` itself (`Δ = c` in
  characteristic `2`) and has `#E[2] = 1`.  So the converse is proved over an arbitrary field at
  **+0** modules, and `𝔽₂(t)` is wanted for **non-vacuity of the imperfect side** and for nothing
  else.  ⚠️ **The `+2` figure the bullet published was right about the module it named and wrong
  about the route**, which is the one measurement worth carrying away from this file:
  `Mathlib.FieldTheory.RatFunc.Basic` is `+2`, but `RatFunc.X` is declared in
  `Mathlib.FieldTheory.RatFunc.AsPolynomial` at **+299** and `RatFunc.intDegree` — the three-line
  proof that `t` is not a square — in `Mathlib.FieldTheory.RatFunc.Degree` at **+300**.  See
  `### ⚠️ The imperfect witness` and the three-imports section of this docstring.
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

**Three certificates: one per branch of the dichotomy, and one for the branch the dichotomy does
NOT reach.**

* **Supersingular**, `#E[2] = 1`: `EllipticCurves.Fixture.y2AddYEqX3` at `R = ZMod 2` —
  `y² + y = x³`, with `a₁ = 0` and `a₃ = 1`.  The rest of this section is about that one.
* **Ordinary**, `#E[2] = 2`: `y² + xy = x³ + 1`, the tuple `⟨1, 0, 0, 0, 1⟩`, ⚠️ **over an ARBITRARY
  field of characteristic `2` and then instantiated at `ZMod 2`** — see
  the section heading *"The ordinary branch, certified over an ARBITRARY field of characteristic
  `2`"* below, which says why `Fixtures` cannot supply this one at all and not merely why it does
  not.
* ⚠️ **Ordinary and yet `#E[2] = 1`**: `y² + xy = x³ + t` over `𝔽₂(t)`, the tuple
  `⟨1, 0, 0, 0, t⟩`.  ⚠️ **This is the first curve in the tree with `a₁ ≠ 0` and `#E[2] ≠ 2`**, and
  it is what makes `card_torsion_two_le_two_of_char_two`'s *"the bound is sharp"* and
  `card_torsion_two_of_sq_surjective_of_char_two`'s hypothesis both honest: without it the `= 2`
  row of the dichotomy could have been an unconditional theorem for all this file showed.  It also
  supplies the non-vacuity of the imperfect side of
  `perfectField_iff_forall_card_torsion_two_eq_two_of_char_two` — see
  `### ⚠️ The imperfect witness` at the foot of the file.

⚠️ **`EllipticCurves.Fixtures` serves no characteristic-`2` CERTIFICATE and says in terms why** —
*"The finite-field certificates are deliberately NOT served here, and this paragraph no longer
says how many there are"*.  ⚠️⚠️ **That wording is the repair of a numeral and not a rephrasing,
and the sentence standing here used to quote the numeral**: the clause read *"and there are FOUR
of them … In full, so that no sweep has to rediscover it"*, and neither half is live text in
`Fixtures` any more: the numeral survives there only as a retired quotation keyed to `0db45cd`,
and the second half not at all — `grep -c 'no sweep has to rediscover'` over that file is **0**.
The list the numeral stood over kept being extended, which `Fixtures` records as a sha-keyed
series, this file's own row being one of the rows it did not contain.  ⚠️ **It does declare the
CURVE**: the definition instantiated above is `Fixtures`' own `y2AddYEqX3`, whose docstring names
this base and this gap in terms — *"Over `ZMod 2` the same equation is supersingular … that is
the char-`2` certificate described in the module docstring, and it is not served here"*.  ⚠️
**And the certificates for this curve over this base are named here rather than counted**:
`exampleCurveChar2` (`EllipticCurves.FunctionField.NegYGalois`), `exampleCurveTwo`
(`EllipticCurves.FunctionField.NegYInvolution`) and `exampleCurveNegYGalois`
(`EllipticCurves.FunctionField.NegYGaloisGroup`), all `⟨0,0,1,0,0⟩`, all proving `IsElliptic` by
`decide +kernel`; and `EllipticCurves.FunctionField.FunctionFieldGaloisDescent`'s `Nonvacuity`
section uses `y2AddYEqX3` over `ZMod 2` **without certifying it** — that file declares no
`IsElliptic` instance and takes `[W.IsElliptic]` in no statement, so it is a SITE and not a
certificate, which is the shape distinction `EllipticCurves.Torsion.ThreeTorsionCharThree`
carries and the reason no size is published for either reading.  ⚠️ **So the reason a further
certificate is supplied here is NOT that there is none — it is that every one of those sites is
`private` or an `example` and every one lives under `FunctionField/`, which is DOWNSTREAM of
`Torsion/`.** `Fixtures`' own rule that *"`private` hides a NAME, not an INSTANCE"* reaches only
downstream of the declaring module, which is the wrong direction here, and an import edge that
fixed it would invert the tree.  The instance below is therefore built by the precedents' own
one-line recipe — `isElliptic_iff`, `isUnit_iff_ne_zero`, `decide +kernel` — rather than by a
hand `Δ` computation, and `Fixtures`' *"a later sweep should not 'finish the job' by deleting
them"* protects this one too. ⚠️ **No `Fact (Nat.Prime 2)` is declared here**: Mathlib's global
`Nat.fact_prime_two` is what resolves, and `Field (ZMod 2)` synthesises from
`EllipticCurves.Torsion.TwoTorsion` and `Mathlib.Algebra.Field.ZMod` alone — ⚠️ **the third
import, `Mathlib.FieldTheory.Perfect`, plays no part in it.**

`Δ = −27 · b₆² = −27 = 1` in `ZMod 2`, which is the discriminant `NegYGalois` records for the same
curve.  The certificate is `#E[2] = 1` **exactly**, not a bound, and the `≠ 4` corollary is
instantiated beside it so that the statement this file exists to contradict is contradicted at a
concrete curve.

## ⚠️ Three Mathlib imports beyond `TwoTorsion`, and the third is the only one that costs anything

`Mathlib.Algebra.Field.ZMod` is imported for **`Field (ZMod 2)`** alone.  ⚠️ **Nothing in the theory
above needs it** — every public statement is over an abstract `[Field F]` — and it is here because
this tree has no characteristic-`2` field to certify against otherwise.  **A reader pricing this
file's closure should subtract that edge from the mathematics and charge it to the certificates.**

`Mathlib.FieldTheory.Perfect` is imported for **`PerfectField`**, `surjective_frobenius`,
`PerfectRing.ofSurjective` and `PerfectRing.toPerfectField`, used by
`perfectField_iff_sq_surjective_of_char_two` and through it by two more statements.
⚠️ **It is FREE, measured and not assumed**: it is already in this file's closure by the route
`Mathlib.FieldTheory.Perfect` ← `Mathlib.FieldTheory.IsAlgClosed.Basic` ←
`EllipticCurves.Torsion.TwoTorsion`, so the explicit line adds **0** resolvable modules.
⚠️ **The line is written anyway rather than relying on the transitive reach**, because the name
would otherwise resolve only for as long as `TwoTorsion` happens to keep an import it does not need
for `PerfectField`'s sake.

`Mathlib.FieldTheory.RatFunc.Basic` is imported for the **imperfect witness** and nothing else, and
it costs **+2** resolvable modules (`6 → 6` inside `EllipticCurves`) at `e4345ae`.  ⚠️ **That is
exactly the figure `## ⚠️ What is *not* here` published when it declared the witness absent — and
the route it was published for costs one hundred and fifty times as much.**  Measured at the same
sha, against the same base of three imports, **by the elaborator**:

| module | delta | what it would buy |
|---|---|---|
| `Mathlib.FieldTheory.RatFunc.Defs` | **+1** | `RatFunc`, `induction_on'` |
| `Mathlib.FieldTheory.RatFunc.Basic` | **+2** | `induction_on`, `algebraMap_injective` — TAKEN |
| `Mathlib.FieldTheory.RatFunc.AsPolynomial` | **+299** | `RatFunc.X`, `num`, `denom` |
| `Mathlib.FieldTheory.RatFunc.Degree` | **+300** | `intDegree`, the three-line non-square proof |

⚠️ **The last two cells were published as `+182` and `+183` for two rounds and were short by 117
each.**  The `+1`, the `+2` and `Perfect`'s `+0` reproduced on every instrument this board has run;
the two three-figure cells reproduced on none.  **The added sets, because a delta is checkable only
when its set is:** `Defs` adds itself alone, `Basic` adds exactly `{RatFunc.Basic, RatFunc.Defs}`
— printable in full — and ⚠️ **`Degree`'s set is `AsPolynomial`'s plus exactly ONE module,
`RatFunc.Degree` itself**, which is a measurement (`comm -13`, one line each way) and not the
assumption a reader might take the adjacent `299`/`300` for.  All **299** are `Mathlib.*` — **0**
from `Batteries`, `Std`, `Init` or `Lean` — so no package-scope reading rescues the smaller figure;
the split is **Topology 122**, RingTheory 55, Algebra 31, Order 25, FieldTheory 15, Combinatorics
13, Data 12, LinearAlgebra 11, and **15** across five more.

⚠️ **So `t` is written `algebraMap 𝔽₂[X] 𝔽₂(X) X` and not `RatFunc.X`, and *"`t` is not a square"*
is a `natDegree` parity over `𝔽₂[t]` and not an `intDegree` parity over `𝔽₂(t)`.**  ⚠️ **And a
TOTAL is not an ATTRIBUTION.** `AsPolynomial` adds five imports over `Basic`; priced one at a time
on top of base + `Basic`, they are

| `AsPolynomial`'s new import | marginal |
|---|---|
| `Mathlib.RingTheory.EuclideanDomain` | **+0** |
| `Mathlib.RingTheory.Localization.FractionRing` | **+0** |
| `Mathlib.RingTheory.Polynomial.Content` | **+0** |
| `Mathlib.RingTheory.Valuation.IsTrivialOn` | **+7** |
| `Mathlib.RingTheory.DedekindDomain.AdicValuation` | ⚠️ **+295** |

— so the `+299` is carried by `AdicValuation`, which at mathlib `81a5d25` is the `public import`
at `FieldTheory/RatFunc/AsPolynomial.lean`:`10`, ⚠️ **three lines above** the plain `import` of
`IsTrivialOn` at `:13` that this file used to blame for the whole of it, with
`Localization.FractionRing` (`:11`) and `Polynomial.Content` (`:12`) standing between them.
⚠️ **The table above is ordered by MARGINAL and not by source line**, which is why it prints those
two rows in the opposite order to the file.  ⚠️ **Marginals
are not additive and the residue accounts for itself exactly**: the two added sets share **6**
modules, so their union is `295 + 7 − 6 = 296`, and the `299` is that union plus precisely three
names — `AsPolynomial` itself and the `{RatFunc.Basic, RatFunc.Defs}` of the `+2`, which the base
of the marginal table already carries.  ⚠️ **`Valuation` is 13 of the 299 and `DedekindDomain` is
3**, so the prose *"valuations, Dedekind domains and a topology stack"* leads with the 16 and
trails with the 122.  ⚠️ **A price quoted for a NAME is not a price for the module that DECLARES
it**, which is the shape of the error this table corrects — and the same error one level down, a
price quoted for a MODULE and not for the import that carries it, is what the marginal table
corrects in turn.

⚠️ **A closure COUNT carries a sha and a membership claim does not** (`README.md`,
`## Import-closure figures`), and ⚠️ **the arbiter of a module count is the ELABORATOR and not a
walker.**  The instrument behind every delta above is four lines and parses nothing:

```
  import <each base module>
  import <the candidate>
  run_meta do for m in (← Lean.getEnv).header.moduleNames do IO.println m
```

then `lake env lean` the probe, `sort -u`, and take the added set by `comm -13`.
⚠️ **`moduleNames` INCLUDES the seed**, so a figure read off it is module-*included*; subtract `1`
for this board's module-*excluded* convention — the control
`EllipticCurves.TateModule.MatrixRepMod` reads **41** included and **40** excluded, which is the
landed `40`, to the unit.  Base here reads **3796** module-included.

⚠️ **That control is an `EllipticCurves`-only measurement and it is blind to the half that decided
these cells.**  Seeded on `^module$` or `^public import `: **0** of this project's **440** tracked
`.lean` files use either, against **8261** of Mathlib's **8264**.  ⚠️ **So a walker's handling of
the module system is UNEXERCISED by the control and DECISIVE for the disputed figure**, and the
`+182` that stood here for two rounds passed that control on the instrument that produced it.
⚠️ **State which HALF of an instrument a control validates — if the control's population and the
figure's population differ in a property that changes the answer, the control is decoration.**

⚠️ **And the rule this paragraph used to state drew the boundary in the wrong place.** It said that
every decision here rests on a *delta* and a *membership boolean*, *"both of which reproduce across
instruments"*, and treated the ABSOLUTE as the unreliable class — three walkers reported `2511`,
`2423` and the `2518` this paragraph used to quote, and `3796` on Lean is a fourth.  ⚠️ **A delta
is a
DIFFERENCE OF TWO ABSOLUTES and inherits their instrument dependence.** The boundary that holds is
**enumerability, not delta-ness**: `+1` and `+2` reproduce everywhere because their added sets can
be *printed by name*, and a three-figure delta is exactly as instrument-dependent as an absolute.
**So: quote no absolute as a landed control, publish the added set whenever it is small enough to
print, and settle anything larger on the elaborator.**

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

/-! ### The converse: the linear condition PRODUCES a `2`-torsion point

⚠️ **`a₁_mul_add_a₃_eq_zero_of_mem_torsion_two_of_char_two` runs one way only**, and everything
above is a bound for that reason.  The reverse direction splits into two halves that are worth
keeping apart, because ⚠️ **only the second of them binds the characteristic** and ⚠️ **only the
first can fail over a field the caller does not control.** -/

/-- **A point above the linear condition is on the curve — in EVERY characteristic.**

If `a₁x + a₃ = 0` then the Weierstrass equation's entire `y`-linear part
`a₁xy + a₃y = (a₁x + a₃)y` vanishes, and what is left is `y² = x³ + a₂x² + a₄x + a₆`; so any square
root of that cubic's value at `x` is the `y`-coordinate of a point.

⚠️ **No `(2 : F) = 0` anywhere**, and that is not an oversight: the collapse of the `y`-linear part
follows from `hlin` alone.  What characteristic `2` contributes is that `hlin` is *satisfiable* —
away from it the `2`-torsion condition `2y + a₁x + a₃ = 0` pins `y` instead, and `hlin` is an extra
constraint rather than the whole of one.  `[W.IsElliptic]` is spent on `equation_iff_nonsingular`
and on nothing else. -/
theorem nonsingular_of_a₁_mul_add_a₃_eq_zero_of_sq_eq [W.IsElliptic] {x y : F}
    (hlin : W.a₁ * x + W.a₃ = 0) (hy : y ^ 2 = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) :
    W.Nonsingular x y := by
  rw [← equation_iff_nonsingular, equation_iff]
  linear_combination hy + y * hlin

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

/-- **Every affine point whose `x` satisfies the linear condition is `2`-torsion**, in
characteristic `2` — the converse of `a₁_mul_add_a₃_eq_zero_of_mem_torsion_two_of_char_two`.

⚠️ **The `y`-coordinate is unconstrained here, and `hy` is not a hypothesis.**
`mem_torsion_two_some_iff` asks for `2y + a₁x + a₃ = 0`; the characteristic kills the `2y` and what
is left is exactly `hlin`.  So *given a point*, being `2`-torsion is decided by its `x` alone —
producing the point is the hard half and it is
`nonsingular_of_a₁_mul_add_a₃_eq_zero_of_sq_eq`'s.

⚠️ **No `[W.IsElliptic]`**, matching the forward direction, which has none either. -/
theorem mem_torsion_two_some_of_a₁_mul_add_a₃_eq_zero_of_char_two (h2 : (2 : F) = 0) {x y : F}
    {h : W.Nonsingular x y} (hlin : W.a₁ * x + W.a₃ = 0) : Point.some x y h ∈ W.torsion 2 :=
  (mem_torsion_two_some_iff h).mpr (by linear_combination hlin + y * h2)

/-- **`(x, y) ∈ E[2] ↔ a₁x + a₃ = 0` in characteristic `2`** — the packaged form of the two
directions, and the statement `mem_torsion_two_some_iff` degenerates to once `2 = 0`.

⚠️ **Note what has gone from the right-hand side: the `y` has.**  Away from characteristic `2` the
same `iff` reads `2y + a₁x + a₃ = 0` and *determines* `y` from `x`
(`eq_twoTorsionY_of_mem_torsion_two`, `EllipticCurves.Torsion.TwoTorsion`); here it does not mention
`y` at all, so among the points of `W` being `2`-torsion is a condition on the `x`-coordinate
alone. -/
theorem mem_torsion_two_some_iff_a₁_mul_add_a₃_eq_zero_of_char_two (h2 : (2 : F) = 0) {x y : F}
    {h : W.Nonsingular x y} : Point.some x y h ∈ W.torsion 2 ↔ W.a₁ * x + W.a₃ = 0 :=
  ⟨a₁_mul_add_a₃_eq_zero_of_mem_torsion_two_of_char_two h2,
    mem_torsion_two_some_of_a₁_mul_add_a₃_eq_zero_of_char_two h2⟩

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
two elements.  ⚠️ **The bound is sharp and is not an equality**, and
`card_torsion_two_eq_two_iff_of_a₁_ne_zero_of_char_two` says exactly when it is attained: the one
candidate affine point exists iff a single element of `F` is a square.  ⚠️ **So this statement is
the weak half of a pair and not the file's last word on the count** — see
`card_torsion_two_of_sq_surjective_of_char_two` for the dichotomy. -/
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

/-! ### `#E[2] = 2` exactly, and the obstruction is a single square root -/

/-- **One nonzero `2`-torsion point forces `#E[2] = 2`** over a field of characteristic `2`.

`Nat.card_eq_two_iff'` at `0` asks for a *unique* nonzero element; `P` supplies existence and
`eq_of_mem_torsion_two_of_char_two` supplies uniqueness.  ⚠️ **This is where
`card_torsion_two_le_two_of_char_two`'s bound becomes an equality, and it needs no hypothesis on `F`
beyond the point it is handed** — which is why every strengthening below is about producing that
point and never about counting. -/
theorem card_torsion_two_eq_two_of_ne_zero_of_char_two (h2 : (2 : F) = 0) {P : W.Point}
    (hP : P ∈ W.torsion 2) (hP0 : P ≠ 0) : Nat.card (W.torsion 2) = 2 := by
  refine (Nat.card_eq_two_iff' (0 : W.torsion 2)).mpr ⟨⟨P, hP⟩, ?_, fun Q hQ => ?_⟩
  · exact fun h => hP0 (congrArg Subtype.val h)
  · exact Subtype.ext (eq_of_mem_torsion_two_of_char_two h2 Q.2 hP
      (fun h => hQ (Subtype.ext h)) hP0)

omit [W.IsElliptic] in
/-- **An affine `2`-torsion point on the ordinary branch EXHIBITS the square root** — the shared
engine of `card_torsion_two_eq_two_iff_of_a₁_ne_zero_of_char_two`'s forward direction and of
`torsion_two_eq_bot_of_a₁_ne_zero_of_not_sq_of_char_two`.

`a₁ ≠ 0` cancels in `a₁x' + a₃ = 0 = a₁x + a₃` and pins `x' = x`; the Weierstrass equation at
`(x', y')` minus `y'` times that linear relation is then exactly `y'² = x³ + a₂x² + a₄x + a₆`.

⚠️ **It is `private` because both consumers are in this file and neither statement mentions the
point**, and ⚠️ **it carries no `[W.IsElliptic]`** — it constrains a point rather than building
one. -/
private theorem sq_eq_of_mem_torsion_two_of_a₁_ne_zero_of_char_two (h2 : (2 : F) = 0)
    (ha₁ : W.a₁ ≠ 0) {x : F} (hx : W.a₁ * x + W.a₃ = 0) {x' y' : F} {h' : W.Nonsingular x' y'}
    (hP : Point.some x' y' h' ∈ W.torsion 2) :
    ∃ y : F, y ^ 2 = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
  have e' := a₁_mul_add_a₃_eq_zero_of_mem_torsion_two_of_char_two h2 hP
  have hxx : x' = x := mul_left_cancel₀ ha₁ (by linear_combination e' - hx)
  subst hxx
  exact ⟨y', by linear_combination (equation_iff x' y').mp h'.left - y' * e'⟩

/-- **`#E[2] = 2` exactly when the cubic's value at the one candidate `x` is a square** —
characteristic `2`, the ordinary branch `a₁ ≠ 0`, and ⚠️ **no hypothesis on `F` whatsoever.**

`a₁ ≠ 0` makes `hlin` determine `x` outright — it is `a₃ / a₁`, and any `x` satisfying `hx` is that
one — so the whole question of whether `E[2]` is larger than `⊥` reduces to whether
`x³ + a₂x² + a₄x + a₆` has a square root in `F`.

⚠️ **This is the sharp form of `card_torsion_two_le_two_of_char_two`'s *"the bound is sharp and is
not an equality"***: the obstruction is named, it is one square root and not a family of them, and
both directions are proved rather than one.  ⚠️ **Together with
`torsion_two_eq_bot_of_a₁_eq_zero_of_char_two` this decides `#E[2]` for every curve over every field
of characteristic `2`** — `1` when `a₁ = 0`, and `2` or `1` according as the single element
`x³ + a₂x² + a₄x + a₆` of `F` is a square or is not.

⚠️ **`x` is a PARAMETER and not written `a₃ / a₁`**, so that the statement carries no division; a
caller holding `a₁ ≠ 0` gets its `hx` from `field_simp`, which is exactly what
`card_torsion_two_eq_two_of_a₁_ne_zero_of_char_two` below does. -/
theorem card_torsion_two_eq_two_iff_of_a₁_ne_zero_of_char_two (h2 : (2 : F) = 0) (ha₁ : W.a₁ ≠ 0)
    {x : F} (hx : W.a₁ * x + W.a₃ = 0) :
    Nat.card (W.torsion 2) = 2 ↔ ∃ y : F, y ^ 2 = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
  refine ⟨fun hcard => ?_, fun ⟨y, hy⟩ => card_torsion_two_eq_two_of_ne_zero_of_char_two h2
    (mem_torsion_two_some_of_a₁_mul_add_a₃_eq_zero_of_char_two
      (h := nonsingular_of_a₁_mul_add_a₃_eq_zero_of_sq_eq hx hy) h2 hx) (by simp)⟩
  obtain ⟨⟨P, hP⟩, hP0, -⟩ := (Nat.card_eq_two_iff' (0 : W.torsion 2)).mp hcard
  rcases P with _ | ⟨x', y', h'⟩
  · exact absurd (Subtype.ext (show (Point.zero : W.Point) = 0 from rfl)) hP0
  exact sq_eq_of_mem_torsion_two_of_a₁_ne_zero_of_char_two h2 ha₁ hx hP

omit [W.IsElliptic] in
/-- **`E[2]` is trivial on the ordinary branch when the cubic's value is NOT a square** —
characteristic `2`, `a₁ ≠ 0`, and ⚠️ **no hypothesis on `F` beyond the failure it is handed.**

This is the negative half of `card_torsion_two_eq_two_iff_of_a₁_ne_zero_of_char_two`, stated as an
equality rather than as a bound: `a₁ ≠ 0` pins the `x` of any affine `2`-torsion point to the one
`hx` names, and the Weierstrass equation then exhibits its `y` as a square root of
`x³ + a₂x² + a₄x + a₆` — which `hsq` says does not exist.  So no affine point is `2`-torsion at all
and `E[2]` collapses to `⊥`, exactly as it does on the supersingular branch for a different reason
(`torsion_two_eq_bot_of_a₁_eq_zero_of_char_two`).

⚠️ **No `[W.IsElliptic]`.**  All this needs is `sq_eq_of_mem_torsion_two_of_a₁_ne_zero_of_char_two`,
the extraction engine it shares with the `= 2` half, and that does not use it; the
`[W.IsElliptic]` of the `= 2` half enters only through
`nonsingular_of_a₁_mul_add_a₃_eq_zero_of_sq_eq`, which BUILDS a point rather than constraining
one. -/
theorem torsion_two_eq_bot_of_a₁_ne_zero_of_not_sq_of_char_two (h2 : (2 : F) = 0) (ha₁ : W.a₁ ≠ 0)
    {x : F} (hx : W.a₁ * x + W.a₃ = 0)
    (hsq : ¬ ∃ y : F, y ^ 2 = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) :
    W.torsion 2 = ⊥ := by
  refine eq_bot_iff.mpr fun P hP => ?_
  rcases P with _ | ⟨x', y', h'⟩
  · exact AddSubgroup.mem_bot.mpr rfl
  · exact absurd (sq_eq_of_mem_torsion_two_of_a₁_ne_zero_of_char_two h2 ha₁ hx hP) hsq

/-- **`#E[2] = 1` exactly when that same element is NOT a square** — the complement of
`card_torsion_two_eq_two_iff_of_a₁_ne_zero_of_char_two`, and ⚠️ **the two together say that on the
ordinary branch `#E[2]` is decided by one bit of `F`: whether one named element has a square
root.**

⚠️ **The two values `1` and `2` therefore exhaust the ordinary branch as well as the file**, which
`card_torsion_two_le_two_of_char_two` alone does not say — a bound of `2` leaves `0` open, and it is
`card_torsion_two_eq_one_iff_of_a₁_ne_zero_of_char_two` together with its sibling that closes it.
-/
theorem card_torsion_two_eq_one_iff_of_a₁_ne_zero_of_char_two (h2 : (2 : F) = 0) (ha₁ : W.a₁ ≠ 0)
    {x : F} (hx : W.a₁ * x + W.a₃ = 0) :
    Nat.card (W.torsion 2) = 1 ↔ ¬ ∃ y : F, y ^ 2 = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
  refine ⟨fun h1 hex => ?_, fun hsq => ?_⟩
  · rw [(card_torsion_two_eq_two_iff_of_a₁_ne_zero_of_char_two h2 ha₁ hx).mpr hex] at h1
    omega
  · rw [torsion_two_eq_bot_of_a₁_ne_zero_of_not_sq_of_char_two h2 ha₁ hx hsq]
    simp

/-- **`#E[2] = 2` in the ordinary branch over a field whose squaring map is onto.**

The candidate `x` is `a₃ / a₁`, and `hsq` hands over the square root that
`card_torsion_two_eq_two_iff_of_a₁_ne_zero_of_char_two` asks for.  ⚠️ **`hsq` is stated as a bare
`Function.Surjective` on `fun y => y ^ 2` rather than as perfectness or as `[CharP F 2]`**, for the
reason `## On the spelling of the hypothesis` gives: it is the weakest thing the proof uses, and
`card_torsion_two_of_perfectField_of_char_two` below is the instance-level form for callers that
would rather supply `[PerfectField F]`. -/
theorem card_torsion_two_eq_two_of_a₁_ne_zero_of_char_two (h2 : (2 : F) = 0) (ha₁ : W.a₁ ≠ 0)
    (hsq : Function.Surjective fun y : F => y ^ 2) : Nat.card (W.torsion 2) = 2 := by
  have hx : W.a₁ * (W.a₃ / W.a₁) + W.a₃ = 0 := by field_simp; linear_combination W.a₃ * h2
  exact (card_torsion_two_eq_two_iff_of_a₁_ne_zero_of_char_two h2 ha₁ hx).mpr (hsq _)

/-- **`#E[2]` in characteristic `2`, decided: `1` on the supersingular branch and `2` on the
ordinary one**, over any field whose squaring map is onto.

⚠️ **This is the statement `card_torsion_two` (`EllipticCurves.Torsion.TwoTorsion`) has no
analogue of here.**  There `#E[2] = 4` over an algebraically closed field of characteristic `≠ 2`;
the `a₁ = 0` row below is `torsion_two_eq_bot_of_a₁_eq_zero_of_char_two` read as a count and the
`a₁ ≠ 0` row is `card_torsion_two_eq_two_of_a₁_ne_zero_of_char_two`, so ⚠️ **neither value is `4`
and the branch that the classical count would call *generic* is the one that gives `2`.** -/
theorem card_torsion_two_of_sq_surjective_of_char_two (h2 : (2 : F) = 0)
    (hsq : Function.Surjective fun y : F => y ^ 2) :
    Nat.card (W.torsion 2) = if W.a₁ = 0 then 1 else 2 := by
  by_cases h1 : W.a₁ = 0
  · rw [if_pos h1, torsion_two_eq_bot_of_a₁_eq_zero_of_char_two h2 h1]; simp
  · rw [if_neg h1]; exact card_torsion_two_eq_two_of_a₁_ne_zero_of_char_two h2 h1 hsq

omit [DecidableEq F] in
/-- **`F` is perfect exactly when its squaring map is onto**, in characteristic `2` — the bridge
between this file's hypothesis convention and Mathlib's `PerfectField`.

⚠️ **This is a statement about `F` alone and mentions no curve**, and it is in this file because
the tree has no characteristic-`2` field-theory module and **two** consumers in it:
`card_torsion_two_of_perfectField_of_char_two`, which used to carry the forward half inline, and
`perfectField_iff_forall_card_torsion_two_eq_two_of_char_two`, which is this `iff` composed with the
family one.

⚠️ **Both of those and the `𝔽₂(t)` certificate below use the FORWARD half, and the reverse half has
no consumer in this file at all.**  Measured rather than read: `.mpr` occurs on neither this name
nor the family one anywhere below, and `Iff.mp` of an `Iff.trans` is the composite of the two
`.mp`s — so `exampleNotPerfectFieldRatFunc`, which derives `¬ P` from `P → Q` and `¬ Q`, can only be
using `PerfectField F → Surjective (· ^ 2)`.  ⚠️ **The reverse half is stated because it is the
other half of a natural `iff` and NOT because anything here consumes it**; nothing in this file ever
proves `PerfectField` of anything.  ⚠️ **`#2249` commissioned it with the opposite reason** — *"the
certificate of item 4 needs the reverse half"* — **and that reason was wrong about the tree and not
only about a branch.**

⚠️ **Two conversions happen inside, and both are the price of this file's hypothesis convention.**
`[PerfectField F]` plus `[ExpChar F 2]` gives `PerfectRing F 2` (Mathlib's
`PerfectField.toPerfectRing`), whose `surjective_frobenius` is the forward direction; the reverse is
`PerfectRing.ofSurjective` — a field is reduced, so surjectivity of the Frobenius is enough —
followed by `PerfectRing.toPerfectField`.  But `ExpChar F 2` is stated in terms of `CharP F 2`, and
this file binds `(2 : F) = 0` instead.  The bridge is four lines and it is `2`'s primality that
carries it: `ringChar F ∣ 2` from `h2`, then `ringChar F ≠ 1` from `Nontrivial F`, and
`Nat.dvd_prime` leaves `ringChar F = 2`.  ⚠️ **So the `CharP` conversion that
`## On the spelling of the hypothesis` promises *"is available to any caller"* is exercised here,
in the one direction that section did not spell out — and it would NOT transpose to a composite
modulus.** -/
theorem perfectField_iff_sq_surjective_of_char_two (h2 : (2 : F) = 0) :
    PerfectField F ↔ Function.Surjective fun y : F => y ^ 2 := by
  haveI : CharP F 2 := by
    refine ringChar.of_eq ?_
    rcases (Nat.dvd_prime Nat.prime_two).mp (ringChar.dvd (by exact_mod_cast h2)) with h | h
    · exact absurd h CharP.ringChar_ne_one
    · exact h
  haveI : ExpChar F 2 := ExpChar.prime Nat.prime_two
  refine ⟨fun _ c => ?_, fun hsq => ?_⟩
  · obtain ⟨y, hy⟩ := surjective_frobenius F 2 c
    exact ⟨y, by simpa [frobenius_def] using hy⟩
  · haveI : PerfectRing F 2 := PerfectRing.ofSurjective F 2 fun c => by
      obtain ⟨y, hy⟩ := hsq c
      exact ⟨y, by simpa [frobenius_def] using hy⟩
    exact PerfectRing.toPerfectField F 2

/-- **The same dichotomy over a perfect field**, which is the form the module docstring's
`## ⚠️ What is *not* here` used to declare absent.

⚠️ **The `CharP` bridge this proof used to carry inline is now
`perfectField_iff_sq_surjective_of_char_two`**, whose FORWARD half is the whole of what this proof
needs.  ⚠️ **That bridge is stated in both directions even so, and its own docstring says why** —
the reverse half has no consumer in this file, the imperfect certificate below included. -/
theorem card_torsion_two_of_perfectField_of_char_two [PerfectField F] (h2 : (2 : F) = 0) :
    Nat.card (W.torsion 2) = if W.a₁ = 0 then 1 else 2 :=
  card_torsion_two_of_sq_surjective_of_char_two h2
    ((perfectField_iff_sq_surjective_of_char_two h2).mp ‹PerfectField F›)

end Torsion

/-! ### ⚠️ The FAMILY reading: `F` is perfect exactly when EVERY ordinary curve over it has
`#E[2] = 2`

`card_torsion_two_of_perfectField_of_char_two` is one half of a sentence this file's
`## ⚠️ What is *not* here` used to carry — *"`#E[2] = 2` holds exactly when `F` is perfect"* — read
of the whole family of curves over `F` rather than of one of them.  ⚠️ **The converse half is the
statement below, and it needs NO imperfect field to state and none to prove**: the witnessing curve
is built over `F` itself out of whichever element has no square root.

⚠️ **That is a correction to the reason the absence was recorded with.**  The bullet said the
converse *"needs an imperfect `F` and a curve witnessing the failure (`𝔽₂(t)`, `a₆ = t`)"* and
priced the `RatFunc` edge accordingly.  ⚠️ **A universally quantified statement over all curves
does not need a field where it fails** — `𝔽₂(t)` is wanted only to certify that the *imperfect*
side of the `↔` is inhabited, which is what `### ⚠️ The imperfect witness` at the foot of this file
does, and that is a non-vacuity question and not a mathematical one. -/

section FamilyReading

/-- `y² + xy = x³ + c`, the tuple `⟨1, 0, 0, 0, c⟩` over an arbitrary commutative ring — the
**ordinary** family, `a₁ = 1`, one curve for each `c`.

⚠️ **The whole family is here and not just `c = 1`**, because it is what carries the converse half
of the family reading: over a field of characteristic `2` its candidate `x` is `a₃ / a₁ = 0` and
the cubic's value there is `a₆ = c`, so `⟨1, 0, 0, 0, c⟩` has `#E[2] = 2` exactly when `c` is a
square.  ⚠️ **One curve per element of `F`, each detecting exactly one square root** — that is the
whole proof of `sq_surjective_iff_forall_card_torsion_two_eq_two_of_char_two`.

⚠️⚠️ **This docstring used to say that it belongs in `EllipticCurves.Fixtures` and is here
instead, because that module *"serves no `a₁ ≠ 0` curve at all"*.  ⛔ THAT REASON IS RETIRED: the
family IS now in `EllipticCurves.Fixtures`**, as `y2AddXYEqX3AddC`, with the same tuple and the
same parameter, and `curveOrdinaryCharTwo_eq` below pins this definition to it rather than leaving
the two unrelated (`#2345`).  ⚠️ **What keeps the local definition is call sites and not the
import**: `Fixtures` is already in this file's import closure, and the name has code occurrences
throughout this file, several of them inside the proof of
`sq_surjective_iff_forall_card_torsion_two_eq_two_of_char_two`, so **retiring it is a separate job**
(`#2345` stage 2).  ⚠️ **No count is given here on purpose**: the population grows, and the pin
below is itself an occurrence, so a numeral here is one behind the tree in the hunk that writes it.
⚠️ **The tuple at `c = 1` is `EllipticCurves.Torsion.TriplingSurjective`'s `curveChar2`**, where it
is `private` and therefore unreachable by name, and where the point taken on it is `(1, 0)` — a
point with `y ≠ negY x y`, so *not* `2`-torsion.  **Same curve, opposite point, for opposite
reasons.** -/
private def curveOrdinaryCharTwo {R : Type*} [CommRing R] (c : R) : Affine R := ⟨1, 0, 0, 0, c⟩

/-- **`curveOrdinaryCharTwo` IS `EllipticCurves.Fixture.y2AddXYEqX3AddC`**, at every base and every
parameter and not merely at `c = 1`: `curveOrdinaryCharTwo c = y2AddXYEqX3AddC R c`.

⚠️ **This is the relation the docstring above used to assert and could not prove**, because the
shared definition did not exist.  It holds by `rfl`. -/
private theorem curveOrdinaryCharTwo_eq {R : Type*} [CommRing R] (c : R) :
    curveOrdinaryCharTwo c = EllipticCurves.Fixture.y2AddXYEqX3AddC R c := rfl

/-- `Δ = −c − 432c²` on that curve, hence `Δ = c` in characteristic `2` and `IsElliptic` exactly
when `c ≠ 0`.

`b₂ = a₁² = 1`, `b₄ = 0`, `b₆ = 4c`, `b₈ = a₁²a₆ = c`, so
`Δ = −b₂²b₈ − 8b₄³ − 27b₆² + 9b₂b₄b₆ = −c − 432c²`, and `−c − 432c² − c = (−c − 216c²) · 2`.
⚠️ **At `c = 1` this is `−433`**, which is the number the `ZMod 2` certificate below is stated
with, and `−433 = 1 − 217 · 2`.

⚠️ **`c ≠ 0` is not a side condition, it is the whole condition**: `Δ = c` in characteristic `2`,
so this family is singular at exactly one value of the parameter and elliptic at every other. -/
private theorem isElliptic_curveOrdinaryCharTwo (h2 : (2 : F) = 0) {c : F} (hc : c ≠ 0) :
    (curveOrdinaryCharTwo c).IsElliptic := by
  have hΔ : (curveOrdinaryCharTwo c).Δ = c := by
    simp only [curveOrdinaryCharTwo, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    linear_combination (-c - 216 * c ^ 2) * h2
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, hΔ]
  exact hc

/-- ⚠️ **The family reading, in its weakest form: squaring is onto `F` exactly when every ordinary
elliptic curve over `F` has `#E[2] = 2`** — characteristic `2`, and no other hypothesis on `F`.

`←` is `card_torsion_two_eq_two_of_a₁_ne_zero_of_char_two`, one curve at a time.
`→` is the converse this file used to record as absent: given `c : F`, the curve
`⟨1, 0, 0, 0, c⟩` is elliptic as soon as `c ≠ 0` (its `Δ` **is** `c`), its `a₁` is `1 ≠ 0`, and the
hypothesis at it hands back the square root of `c` that
`card_torsion_two_eq_two_iff_of_a₁_ne_zero_of_char_two` extracts.  ⚠️ **`c = 0` is the one value
the family cannot test, and it needs no test: `0 = 0²`.**

⚠️ **The quantifier is over curves, not over fields**, which is why no imperfect field appears in
the proof and none is needed to state it. -/
theorem sq_surjective_iff_forall_card_torsion_two_eq_two_of_char_two [DecidableEq F]
    (h2 : (2 : F) = 0) :
    (Function.Surjective fun y : F => y ^ 2) ↔
      ∀ W : Affine F, W.IsElliptic → W.a₁ ≠ 0 → Nat.card (W.torsion 2) = 2 := by
  refine ⟨fun hsq W hW ha₁ => ?_, fun hall c => ?_⟩
  · haveI := hW
    exact card_torsion_two_eq_two_of_a₁_ne_zero_of_char_two h2 ha₁ hsq
  · rcases eq_or_ne c 0 with rfl | hc
    · exact ⟨0, by ring⟩
    · haveI := isElliptic_curveOrdinaryCharTwo h2 hc
      obtain ⟨y, hy⟩ := (card_torsion_two_eq_two_iff_of_a₁_ne_zero_of_char_two
        (W := curveOrdinaryCharTwo c) h2 (by simp [curveOrdinaryCharTwo]) (x := 0)
        (by simp [curveOrdinaryCharTwo])).mp
        (hall (curveOrdinaryCharTwo c) (isElliptic_curveOrdinaryCharTwo h2 hc)
          (by simp [curveOrdinaryCharTwo]))
      exact ⟨y, by simpa [curveOrdinaryCharTwo] using hy⟩

/-- ⚠️ **The family reading, as the sentence `## ⚠️ What is *not* here` carries it: `F` is PERFECT
exactly when every ordinary elliptic curve over `F` has `#E[2] = 2`**, in characteristic `2`.

This is `sq_surjective_iff_forall_card_torsion_two_eq_two_of_char_two` composed with
`perfectField_iff_sq_surjective_of_char_two`, and ⚠️ **it is the statement, in both directions,
that `card_torsion_two_of_perfectField_of_char_two` is the forward half of.**  Read of a SINGLE
curve the same words are false, and `exampleCardTorsionTwoOrdinaryOfCharTwo` below refutes them;
`## ⚠️ What is *not* here` says which reading is which. -/
theorem perfectField_iff_forall_card_torsion_two_eq_two_of_char_two [DecidableEq F]
    (h2 : (2 : F) = 0) :
    PerfectField F ↔ ∀ W : Affine F, W.IsElliptic → W.a₁ ≠ 0 → Nat.card (W.torsion 2) = 2 :=
  (perfectField_iff_sq_surjective_of_char_two h2).trans
    (sq_surjective_iff_forall_card_torsion_two_eq_two_of_char_two h2)

end FamilyReading

/-! ### Non-vacuity over `ZMod 2`

`y² + y = x³`, the supersingular branch.  ⚠️ **No `Fact (Nat.Prime 2)` is declared here** —
Mathlib's global `Nat.fact_prime_two` resolves it and `Field (ZMod 2)` synthesises from
`EllipticCurves.Torsion.TwoTorsion` and `Mathlib.Algebra.Field.ZMod` alone.  The module docstring's
`## Non-vacuity` says why a further `⟨0,0,1,0,0⟩`-over-`ZMod 2` certificate is owed at all, given
the ones the tree already has, and names them there instead of counting them here. -/

section Nonvacuity

open EllipticCurves.Fixture

/-- `IsElliptic` for `y² + y = x³` over `ZMod 2`: `Δ = −27 · b₆² = −27 = 1`, and `1 ≠ 0` there.

⚠️ **This is the one-line recipe the tree's other `⟨0,0,1,0,0⟩`-over-`ZMod 2`
certificates use** — `isElliptic_iff`, `isUnit_iff_ne_zero`, `decide +kernel`.  They are
the rows `EllipticCurves.Fixtures` lists for `FunctionField/NegYGaloisGroup` — whose
base is spelled through a `private abbrev` for `ZMod 2` rather than written out —
`FunctionField/NegYGalois` and `FunctionField/NegYInvolution`.

⚠️⚠️ **The RECIPE is what is named above; the COUNT that used to stand beside it in `Fixtures` is
not, and deliberately so.**  That clause read *"All four prove `IsElliptic` by `decide +kernel`"*,
and `Fixtures` has since retired the numeral in favour of the list itself — naming *this*
paragraph's quotation of it as the thing that should have caught the defect, because this file's
own row was one of the rows that list did not contain.  So the sentence that stood here quoted a
census its own module had falsified, which is why the members are named here and no size is.

⚠️ `EllipticCurves.Fixtures`' own instance for this curve does not reach here — it is stated over a
field where `−27 ≠ 0` is a `norm_num` fact, and `ZMod 2` is not one by that route. -/
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

/-! ### The ordinary branch, certified over an ARBITRARY field of characteristic `2`

⚠️ **The curve is `curveOrdinaryCharTwo 1`, declared with the rest of its family in
`### ⚠️ The FAMILY reading` above**, the ordinary branch of the dichotomy being exactly the
`a₁ ≠ 0` one.  ⚠️⚠️ **This paragraph used to give the reason as `EllipticCurves.Fixtures` serving
*"no curve with `a₁ ≠ 0` at all"*, and used to contrast that with the supersingular certificate of
`## Non-vacuity`, where the curve existed in `Fixtures` and only the `IsElliptic` instance was out
of reach.  ⛔ BOTH HALVES ARE RETIRED: the family IS now in `EllipticCurves.Fixtures`**, as
`y2AddXYEqX3AddC`, so this branch is in the supersingular one's situation and the contrast has
collapsed — ⚠️ **what keeps the local definition is call sites and not the import, and that
argument is made once, at `### ⚠️ The FAMILY reading` above, rather than re-made here** (`#2345`).

⚠️ **This block's base is an arbitrary `[Field F]` with `(2 : F) = 0` and not `ZMod 2`**, because
that is what `## ⚠️ What is *not* here` needs: see
`exampleCardTorsionTwoOrdinaryOfCharTwo`. -/

section Ordinary

open EllipticCurves.Fixture

/-- **`#E[2] = 2` for `y² + xy = x³ + 1` over EVERY field of characteristic `2`** — ⚠️ **no
perfectness, no finiteness and no algebraic closure.**

The candidate `x` is `a₃ / a₁ = 0`, the cubic's value there is `a₆ = 1`, and `1 = 1²` in every
ring — so the square root `card_torsion_two_eq_two_iff_of_a₁_ne_zero_of_char_two` asks for is
present whatever `F` is.

⚠️ **This is what refutes the *"`#E[2] = 2` holds exactly when `F` is perfect"* that the first
bullet of `## ⚠️ What is *not* here` carried before this file proved the ordinary branch**, read of
a single curve: over `𝔽₂(t)` — imperfect, and certified imperfect at the foot of this file — this
curve still has `#E[2] = 2`.  ⚠️ **Read of the whole FAMILY the old sentence is true and is now
a theorem in both directions** (`perfectField_iff_forall_card_torsion_two_eq_two_of_char_two`), and
`## ⚠️ What is *not* here` says which reading is which. -/
private theorem exampleCardTorsionTwoOrdinaryOfCharTwo [DecidableEq F] (h2 : (2 : F) = 0) :
    Nat.card ((curveOrdinaryCharTwo (1 : F)).torsion 2) = 2 := by
  haveI := isElliptic_curveOrdinaryCharTwo (F := F) h2 (one_ne_zero)
  refine (card_torsion_two_eq_two_iff_of_a₁_ne_zero_of_char_two h2 (x := 0)
    (by simp [curveOrdinaryCharTwo]) (by simp [curveOrdinaryCharTwo])).mpr
    ⟨1, by simp [curveOrdinaryCharTwo]⟩

/-- **`#E[2] = 2` over `ZMod 2`** for the same curve — ⚠️ **the non-vacuity of the statement
above**, whose hypothesis `(2 : F) = 0` no field in this file's closure had been shown to satisfy on
the ordinary branch. -/
private theorem exampleCardTorsionTwoOrdinaryZModTwo :
    Nat.card ((curveOrdinaryCharTwo (1 : ZMod 2)).torsion 2) = 2 :=
  exampleCardTorsionTwoOrdinaryOfCharTwo (by decide)

/-- **Squaring is onto `ZMod 2`**, so `card_torsion_two_of_sq_surjective_of_char_two`'s hypothesis
is satisfiable — and `ZMod 2` is a finite field, hence perfect, so
`card_torsion_two_of_perfectField_of_char_two` applies to it too. -/
private theorem exampleSqSurjectiveZModTwo : Function.Surjective fun y : ZMod 2 => y ^ 2 := by
  decide

/-- **The dichotomy at BOTH of its branches over `ZMod 2`**: `2` on `⟨1, 0, 0, 0, 1⟩` and `1` on
`y² + y = x³`.  ⚠️ **The `if` is discharged by `decide` on `a₁` in both halves, so this checks the
branch selector and not only the two values** — and the two halves are the two certificates this
file carries over `ZMod 2`, reached through one theorem instead of two. -/
private theorem exampleCardTorsionTwoDichotomyZModTwo :
    Nat.card ((curveOrdinaryCharTwo (1 : ZMod 2)).torsion 2) = 2 ∧
      Nat.card ((y2AddYEqX3 (ZMod 2)).torsion 2) = 1 := by
  haveI := isElliptic_curveOrdinaryCharTwo (F := ZMod 2) (by decide) (one_ne_zero)
  refine ⟨?_, ?_⟩
  · rw [card_torsion_two_of_sq_surjective_of_char_two (by decide) exampleSqSurjectiveZModTwo]
    decide
  · rw [card_torsion_two_of_sq_surjective_of_char_two (by decide) exampleSqSurjectiveZModTwo]
    decide

end Ordinary

/-! ### ⚠️ The imperfect witness: `𝔽₂(t)`, and the ordinary branch attaining `1`

⚠️ **This is the row `## ⚠️ What is *not* here` declared absent and priced at `+2`.**  The price is
paid and the figure is the one that was published — but ⚠️ **the obvious route to it costs `+300`
and not `+2`**, which is the one measurement in this block worth carrying away: see
the three-imports section of the module docstring, where that cell is keyed to the elaborator.

Everything here is `private`: the statements are certificates that the two sides of
`perfectField_iff_forall_card_torsion_two_eq_two_of_char_two` are both inhabited, and no consumer
in this tree wants `𝔽₂(t)` by name. -/

section Imperfect

/-- **`𝔽₂(t)` has characteristic `2`**, through `charP_of_injective_algebraMap` on the structure map
from `ZMod 2` — which is injective because `ZMod 2` is a field. -/
private theorem two_eq_zero_ratFunc : (2 : RatFunc (ZMod 2)) = 0 := by
  haveI : CharP (RatFunc (ZMod 2)) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (RatFunc (ZMod 2))).injective 2
  exact_mod_cast CharP.cast_eq_zero (RatFunc (ZMod 2)) 2

/-- ⚠️ **`t` is not a square in `𝔽₂(t)`** — so `𝔽₂(t)` is imperfect, and this is the one fact the
whole block rests on.

⚠️ **The proof is a degree parity and it is written that way ON PURPOSE.**  Mathlib's `intDegree`
gives the same contradiction in three lines, but `RatFunc.intDegree` lives in
`Mathlib.FieldTheory.RatFunc.Degree`, which costs **+300** resolvable modules here; the route
below needs `Mathlib.FieldTheory.RatFunc.Basic` and nothing else, at **+2**.  Writing
`t` as `algebraMap _ _ Polynomial.X` rather than as `RatFunc.X` is part of the same economy —
⚠️ **`RatFunc.X` itself is declared in `Mathlib.FieldTheory.RatFunc.AsPolynomial`, at `+299`.**

`RatFunc.induction_on` writes any `y` as `p / q` with `q ≠ 0`; clearing denominators gives
`p² = X · q²` in `𝔽₂[t]`, and `natDegree` reads `2 · deg p = 1 + 2 · deg q`, which `omega`
refuses. -/
private theorem not_sq_ratFunc_X :
    ¬ ∃ y : RatFunc (ZMod 2), y ^ 2 = algebraMap (ZMod 2)[X] (RatFunc (ZMod 2)) X := by
  rintro ⟨y, hy⟩
  induction y using RatFunc.induction_on with
  | f p q hq =>
    rw [div_pow, div_eq_iff (by simpa using pow_ne_zero 2 (RatFunc.algebraMap_ne_zero hq))] at hy
    have hpq : p ^ 2 = X * q ^ 2 := by
      apply RatFunc.algebraMap_injective (K := ZMod 2)
      simpa [map_pow, map_mul] using hy
    have hdeg := congrArg natDegree hpq
    rw [natDegree_pow, natDegree_mul X_ne_zero (pow_ne_zero 2 hq), natDegree_X,
      natDegree_pow] at hdeg
    omega

open scoped Classical in
/-- ⚠️ **`#E[2] = 1` on the ORDINARY branch**, for `y² + xy = x³ + t` over `𝔽₂(t)`.

`a₁ = 1 ≠ 0`, so this is the branch `card_torsion_two_of_perfectField_of_char_two` sends to `2`,
and the count is `1` because `t` has no square root.  ⚠️ **It is the first curve in this tree with
`a₁ ≠ 0` and `#E[2] ≠ 2`**, and it is what makes `card_torsion_two_le_two_of_char_two`'s bound
sharp in the direction the `= 2` certificates cannot witness. -/
private theorem exampleCardTorsionTwoImperfectOrdinary :
    Nat.card ((curveOrdinaryCharTwo
      (algebraMap (ZMod 2)[X] (RatFunc (ZMod 2)) X)).torsion 2) = 1 := by
  haveI := isElliptic_curveOrdinaryCharTwo two_eq_zero_ratFunc
    (RatFunc.algebraMap_ne_zero (X_ne_zero (R := ZMod 2)))
  refine (card_torsion_two_eq_one_iff_of_a₁_ne_zero_of_char_two two_eq_zero_ratFunc (x := 0)
    (by simp [curveOrdinaryCharTwo]) (by simp [curveOrdinaryCharTwo])).mpr ?_
  simpa [curveOrdinaryCharTwo] using not_sq_ratFunc_X

open scoped Classical in
/-- ⚠️ **The converse half of the family reading, witnessed: NOT every ordinary elliptic curve over
`𝔽₂(t)` has `#E[2] = 2`** — the right-hand side of
`perfectField_iff_forall_card_torsion_two_eq_two_of_char_two` failing at a concrete field. -/
private theorem exampleNotForallCardTorsionTwoEqTwoRatFunc :
    ¬ ∀ W : Affine (RatFunc (ZMod 2)), W.IsElliptic → W.a₁ ≠ 0 →
      Nat.card (W.torsion 2) = 2 := by
  intro hall
  have := hall _ (isElliptic_curveOrdinaryCharTwo two_eq_zero_ratFunc
    (RatFunc.algebraMap_ne_zero (X_ne_zero (R := ZMod 2)))) (by simp [curveOrdinaryCharTwo])
  rw [exampleCardTorsionTwoImperfectOrdinary] at this
  omega

open scoped Classical in
/-- ⚠️ **`𝔽₂(t)` is not a perfect field**, read off the failure above through
`perfectField_iff_forall_card_torsion_two_eq_two_of_char_two`.

⚠️ **The direction is the interesting one**: the tree now derives a field-theoretic fact from a
count of `2`-torsion points, rather than the other way round, and the `↔` is what makes that legal.
⚠️ **It is the FORWARD half of both `iff`s that is used here**, `¬ P` following from `P → Q` and
`¬ Q`; see `perfectField_iff_sq_surjective_of_char_two`'s docstring.
This is also the non-vacuity of the imperfect side of that `↔` — without it the statement is true
and empty on one side. -/
private theorem exampleNotPerfectFieldRatFunc : ¬ PerfectField (RatFunc (ZMod 2)) := fun hp =>
  exampleNotForallCardTorsionTwoEqTwoRatFunc
    ((perfectField_iff_forall_card_torsion_two_eq_two_of_char_two two_eq_zero_ratFunc).mp hp)

end Imperfect

end WeierstrassCurve.Affine
