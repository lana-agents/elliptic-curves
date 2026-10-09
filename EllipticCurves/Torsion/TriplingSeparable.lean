/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import EllipticCurves.Torsion.StructureGeneral

/-!
# The tripling polynomial of an `n`-torsion point is separable at every ODD `n`

Let `W` be an elliptic curve over a field `F` with `(2 : F) ≠ 0` and `(n : F) ≠ 0` for an **odd**
`n`, and let `x₀` be a root of `preΨₙ` — the `x`-coordinate of an affine `n`-torsion point.  The
**tripling polynomial** at that index,

```
Φₙ − C x₀ · ΨSqₙ = Φₙ − C x₀ · preΨₙ²        (the second spelling because `n` is odd)
```

has degree `n²` — `natDegree_Φ_sub_C_mul_ΨSq` (`EllipticCurves.Torsion.NsmulSurjective`), whose
statement is `(Φₙ − C x₀ · ΨSqₙ).natDegree = n ^ 2` and which carries **no** `Monic`; monicity is
asserted in that lemma's own docstring prose and nothing below needs it — and its roots are the
`x`-coordinates of the points `P` with `nP = ±S`.  **This file proves it separable**, over an
arbitrary such field.

⚠️ **The file is named for `n = 3` and keeps its four `n = 3` statements verbatim**, because that
is the index `#2216` needs and the one every consumer cites.  They are now **corollaries** of the
general forms, proved by supplying `Odd 3` and `((3 : ℕ) : F) ≠ 0`, so no consumer's signature
moves by a character.  ⚠️ **Round 2 of this file said the general index was blocked because
*"`card_torsion_three` has no general-index form anywhere"*.  That sentence was false** — the
general count is `card_torsion_eq_sq` (`EllipticCurves.Torsion.StructureGeneral`) — **and this round
is its retraction, paid by widening the file rather than by rewording the bullet.**
`## The cost of the general index` below prices what it actually cost.

## ⚠️ This is the OPPOSITE of what happens at `n = 2`, and the discriminator is one line

`EllipticCurves.Torsion.HalvingExtension` opens by recording that the `n = 2` member of this family
is **not** separable and cannot be made so:

> Over an algebraic closure the roots of `Φ₂ - C x₀ · Ψ₂Sq` are the `x`-coordinates of the four
> points `Q` with `2 • Q = S`; `Q` and `-Q` share an `x`-coordinate and `-Q = Q ⊕ S`, because `S`
> is `2`-torsion, so four roots counted with multiplicity sit over at most two distinct values and
> the quartic has a repeated root.

⚠️ **The mechanism generalises, and so does its failure.**  Two points of the fibre of `[n]` over
`S` that share an `x`-coordinate are equal or opposite (`Point.X_eq_iff`), so the fibre's
`x`-coordinates collide only if some `P` and `−P` both lie in it — and they both lie in it exactly
when `nP = S = −nP`, i.e. when `2S = 0`:

* at `n = 2` that is **automatic**, because `S ∈ E[2]`, and the degeneracy is forced;
* at **every odd `n`** it forces `S = 0`, because `n − 2·⌊n/2⌋ = 1` there, so
  `S = (n − 2·⌊n/2⌋)·S = nS − ⌊n/2⌋·(2S) = 0`.  ⚠️ **This argument is FORMALISED**, in the
  `hinj` block of `separable_Φ_sub_C_mul_ΨSq_of_isAlgClosed_of_odd`: `Odd n` gives `n = 2k + 1`
  and then `0 = nS = k•(2S) + S = S`.  Earlier rounds of this file stated it in prose and said it
  was not formalised; that is no longer true and the sentence has been retired rather than left
  standing.

⚠️ **So no perfect-square identity is needed here, and none exists to look for.**  The `n = 2`
route — factor the quartic as `(X² − C (2x₀)·X − C (K/2))²` and adjoin a root of the quadratic — has
no analogue at `n = 3`, and it is not needed: the degree-`9` polynomial is itself separable and can
be adjoined a root of directly.  ⚠️ **`#2216` predicted the opposite** (*"expect the `n = 3`
tripling polynomial to be worse, and price separability before writing anything"*); it is better,
and this file is the price.

## The proof is a count and not a discriminant

No resultant, no Bézout certificate and no derivative computation appears below.  Over an
algebraically closed field:

1. the fibre `{P : nP = S}` is a coset of `E[n]` (`fibreEquivTorsion`) and so has `n²` elements,
   `card_torsion_eq_sq` (`EllipticCurves.Torsion.StructureGeneral`) supplying the count — ⚠️ **at
   every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`, with no parity hypothesis** — and
   `nsmul_surjective_of_two_ne_zero` (`EllipticCurves.Torsion.TwoTorsionOrder`) its nonemptiness;
2. `P ↦ x(P)` is a **bijection** from that fibre to the root set of the tripling polynomial —
   injective by the paragraph above, which is where `Odd n` is spent, surjective because a root `x`
   carries a point `Q` with `nQ = ±S` and `−Q` absorbs the sign;
3. so the polynomial has `n²` distinct roots and degree `n²`, and
   `Polynomial.nodup_roots_iff_of_splits` turns that into `Separable`.

⚠️ **Step 2 needs `ΨSqₙ(x) ≠ 0` at both ends and gets it from two different places.**  At a root of
the tripling polynomial it is `eval_Φ_ne_zero_of_eval_ΨSq_eq_zero`
(`EllipticCurves.Torsion.TwoTorsionOrder`): `Φₙ` and `ΨSqₙ` have no common root, so a common root
would make the polynomial's value `Φₙ(x) ≠ 0`.  At a point of the fibre it is
`nsmul_eq_zero_iff_eval_preΨ_eq_zero` (`EllipticCurves.Torsion.OddTorsionCount`): a point over a
root of `preΨₙ` is `n`-torsion, and `nP = 0 ≠ S`.  ⚠️ The bridge between the two spellings is
`ΨSq_natCast_eq_sq_of_odd` (same file), which is where `Odd n` pays its **second** debt.

⚠️ **The descent to an arbitrary field is `Polynomial.separable_map` and nothing else.**
Separability of a polynomial is invariant under a field extension, `WeierstrassCurve.map_Φ`,
`map_ΨSq` and Mathlib's `map_preΨ` carry the three objects to `AlgebraicClosure F`, and the root
hypothesis travels with them.  **No Galois theory, no splitting field and no normal closure is used
or mentioned below.**

## Main statements

**19** declarations, **8** public and **11** `private`.  The `private` half is **three** outside the
`ℚ` block — `xCoordOf` and `fibreEquivTorsion`, both `def`s, and the `rfl` lemma `xCoordOf_some` —
and **eight** inside it.  ⚠️ `#print axioms` over all eight public statements reaches **0**
`sorryAx` and nothing outside `{propext, Classical.choice, Quot.sound}`, and all eight return all
three.

⚠️ **The eight are four general statements and their four `n = 3` corollaries, paired**, and every
corollary carries the signature it carried before this round.  Every statement carries
`{F : Type*} [Field F] {W : Affine F}` and `[W.IsElliptic]`, and then:

⚠️ **The four pairs, general form first and its `n = 3` corollary second.**  Names are given with
the common prefix `separable_Φ` written out, and no line in the list below is a table row, because
a pair of these names does not fit in one.  ⚠️ **The scope there is the list and not the file**: the
file does contain a table, in `## The cost of the general index`.

1. `separable_Φ_sub_C_mul_ΨSq_of_isAlgClosed_of_odd` /
   `separable_Φ_three_sub_C_mul_ΨSq_of_isAlgClosed`
2. `separable_Φ_sub_C_mul_ΨSq_of_odd` / `separable_Φ_three_sub_C_mul_ΨSq`
3. `separable_Φ_sub_C_mul_preΨ_sq_of_odd` / `separable_Φ_three_sub_C_mul_Ψ₃_sq`
4. `separable_Φ_sub_C_mul_ΨSq_of_mem_torsion_of_odd` /
   `separable_Φ_three_sub_C_mul_ΨSq_of_mem_torsion`

* `WeierstrassCurve.Affine.separable_Φ_sub_C_mul_ΨSq_of_odd` — **the headline**, over an
  **arbitrary** field with `(2 : F) ≠ 0` and `(n : F) ≠ 0` at odd `n`, from
  `(W.preΨ (n : ℤ)).eval x₀ = 0` alone.  ⚠️ It takes **no** `[DecidableEq F]`, **no**
  `[IsAlgClosed F]` and **no** `y₀`: the hypothesis is about one univariate polynomial at one
  element, and the `y`-coordinate of the `n`-torsion point is manufactured inside the proof over
  the closure, where it always exists.
* `WeierstrassCurve.Affine.separable_Φ_three_sub_C_mul_ΨSq` — its corollary, keyed on
  `W.Ψ₃.eval x₀ = 0`, which is the spelling every consumer of this file states.
* `WeierstrassCurve.Affine.separable_Φ_sub_C_mul_preΨ_sq_of_odd` and
  `…separable_Φ_three_sub_C_mul_Ψ₃_sq` — the same statements spelled with an explicit square, which
  is the spelling `exists_nsmul_three_eq_some_of_root`
  (`EllipticCurves.Torsion.TriplingSurjective`) states its own root hypothesis in.  ⚠️ *"a
  hypothesis a caller has to restate before it can discharge it is a hypothesis nobody
  discharges"* — **that theorem's own docstring**, about that very spelling decision, which is a
  stronger citation than a neighbouring statement's would be.
* `WeierstrassCurve.Affine.separable_Φ_sub_C_mul_ΨSq_of_mem_torsion_of_odd` and
  `…separable_Φ_three_sub_C_mul_ΨSq_of_mem_torsion` — keyed on membership of `W.torsion n` rather
  than on the root.  ⚠️ These two are the **only theorems** below that bind `[DecidableEq F]`, and
  they bind it because `W.torsion` does.  ⚠️ **Theorems and not declarations**: the `private def`
  `fibreEquivTorsion` binds it too, from the `variable` line of its enclosing `section Fibre`.
* `WeierstrassCurve.Affine.separable_Φ_sub_C_mul_ΨSq_of_isAlgClosed_of_odd` and
  `…separable_Φ_three_sub_C_mul_ΨSq_of_isAlgClosed` — the closed-field forms the others are proved
  from, stated rather than hidden because the first one's proof is the content and a reader
  checking the count should not have to find it inside a `rw`.  ⚠️ **They bind no `[DecidableEq F]`
  either**, although the proof counts points of a group whose addition needs one: `classical`
  supplies it inside, and `linter.unusedDecidableInType` is what says so — the instance is in the
  *proof* and not in the *type*.

## ⚠️ The cost of the general index, measured

⚠️ **The general index costs exactly one thing and it is an IMPORT, not a missing theorem.**
`card_torsion_eq_sq` (`EllipticCurves.Torsion.StructureGeneral`) is `#E[n] = n²` at every `n` with
`(2 : F) ≠ 0` and `(n : F) ≠ 0`, **with no parity hypothesis**, and it was not in the
36-module import closure this file had before this round.  Measured at `814e3d9`:

| cell | before | after |
|---|---|---|
| this file's transitive `EllipticCurves` closure, self excluded | **36** | **53** |
| direct `import` lines | **3** | ⚠️ **1** |

⚠️ **It is three `import` lines replaced by one and not a fourth added**: `StructureGeneral`'s own
closure **contains all 36** of this file's previous closure, and all three of the previous direct
imports (`OddTorsionCount`, `ThreeTorsionStructure`, `TriplingSurjective`) are inside it.  The
**17** modules the edit adds are `ChordSum`, `Collinearity`, `NetVieta`, `NsmulYCoord`,
`NsmulYPeriodic`, `OmegaCharZero`, `OmegaChordSum`, `OmegaCrux`, `OmegaPairCoprime`, `OmegaThree`,
`OmegaUniversal`, `StructureGeneral`, `TriplingCoords`, `WronskianRecurrence`,
`WronskianSeparable`, `WronskianUniversal` and `UniversalCurve`.

⚠️ **That is a real price and it would have been a perfectly good reason to stay at `n = 3`.  What
it is not is an absence**, and *"no general-index form anywhere"* was the wrong sentence for it —
a claim about the whole tree, written from the lemma the round reached for.  The other four inputs
needed no import at all: `hasXCoordFormula_of_two_ne_zero` (`NsmulOrder`),
`nsmul_surjective_of_two_ne_zero` and `eval_Φ_ne_zero_of_eval_ΨSq_eq_zero` (`TwoTorsionOrder`) and
`ΨSq_natCast_eq_sq_of_odd` (`OddTorsionCount`) were all inside the 36 already.

## ⚠️ What is *not* here

* **No extension field, and no tower.**  This file adjoins nothing.  What `#2216` needs next — a
  finite Galois `N / F` carrying both `#E[3] = 9` and a tripling of `S` — is a *consumer* of the
  statements above and is not attempted here; `EllipticCurves.Torsion.ThreeDivisionField` already
  supplies the first half of it.
* **Nothing at `n = 2`, and it is FALSE there.**  The `n = 2` member of this family is false and
  `EllipticCurves.Torsion.HalvingExtension` says so.  ⚠️ **`Odd n` is therefore load-bearing and
  not a convenience**: it rules out the one index at which the discriminator above is known to
  collapse.  ⚠️ **It is NOT claimed to be sharp** — *sharp* would say the hypothesis cannot be
  weakened, and `Odd n` excludes every even index while only `n = 2` is known to fail.  What happens
  at even `n > 2` is **not decided below** — the `hinj` step needs `2S = 0 → S = 0`, which is what
  parity gives and what a general even index does not.
* **No even index, and no statement that `Odd n` can be weakened.**  ⚠️ **This file does not claim
  that even `n` is unreachable**, only that nothing below reaches it.  ⚠️ **Parity is load-bearing
  at THREE places in `separable_Φ_sub_C_mul_ΨSq_of_isAlgClosed_of_odd` and not at one**: the torsion
  criterion `nsmul_eq_zero_iff_eval_preΨ_eq_zero` (consumed twice), the two-spellings bridge
  `ΨSq_natCast_eq_sq_of_odd` — both `EllipticCurves.Torsion.OddTorsionCount`, and both *binding*
  `Odd n` in their own statements — and the injectivity step.  ⚠️ **The first two are FALSE at even
  `n` and are therefore not steps a round may rewrite**: `WeierstrassCurve.ΨSq_ofNat` is
  `W.ΨSq n = W.preΨ' n ^ 2 * if Even n then W.Ψ₂Sq else 1`, so at an even index the `Ψ₂Sq` factor
  survives, a root of `ΨSqₙ` need not be a root of `preΨₙ`, and the criterion's forward half fails
  for the same factor — a `2`-torsion point is killed by every even `n` without being a root of
  `preΨₙ`.  **Only the injectivity step is merely unproved.**  ⚠️ **So an even-`n` round starts at
  the first of the three, whose parity-free form is already in the closure**:
  `nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic` (`EllipticCurves.Torsion.TwoTorsionOrder`),
  which is what `nsmul_eq_zero_iff_eval_preΨ_eq_zero`'s own proof opens by rewriting with.
* **No claim about irreducibility, and no factorisation.**  `Separable` is squarefreeness plus a
  derivative condition; nothing below says the tripling polynomial is irreducible, and the
  bijection it is proved by says nothing about the `F`-rationality of any of its `n²` roots.
  ⚠️ **What the proof does give for free is that `x₀` is never a root of its own tripling
  polynomial** — a root has `ΨSqₙ ≠ 0` and `x₀` is a root of `preΨₙ` — which is the sentence
  `nS ≠ S` for `S ≠ 0`, and on the fixture below (at `n = 3`) the value there is **`1`**
  (`eval_triplingPoly_zero_y2AddYEqX3`, machine-checked rather than asserted).
* **No `y`-coordinate statement.**  A tower over this polynomial also needs the Weierstrass
  equation solved in `y` at a root; that quadratic is
  `EllipticCurves.Torsion.HalvingExtension`'s `halvingY`, which is **index-free** and already has
  its discriminant computed there (`discrim_halvingY = Ψ₂Sq.eval x`).  It is not restated here.
* **Characteristic `2` and the index.**  ⚠️ **Both are genuinely used and neither is inherited
  decoration**, counted in the proof body of
  `separable_Φ_sub_C_mul_ΨSq_of_isAlgClosed_of_odd`: `(2 : F) ≠ 0` is passed to **six** distinct
  lemmas at **nine** sites — `exists_equation` (×2), `nsmul_eq_zero_iff_eval_preΨ_eq_zero` (×2),
  `hasXCoordFormula_of_two_ne_zero` (×2), `eval_Φ_ne_zero_of_eval_ΨSq_eq_zero`,
  `nsmul_surjective_of_two_ne_zero` and `card_torsion_eq_sq` — and `(n : F) ≠ 0` at exactly
  **one**, `card_torsion_eq_sq`, with `n ≠ 0` derived from it for **two further lemmas not already
  named above** (`natDegree_Φ_sub_C_mul_ΨSq` and `pow_ne_zero`).  ⚠️ **The unit there is the lemma
  and not the site**: as sites the derived `n ≠ 0` is consumed **four** times, the other two being
  inside `eval_Φ_ne_zero_of_eval_ΨSq_eq_zero` and `nsmul_surjective_of_two_ne_zero`, which the `h2`
  list beside it already names.  ⚠️ **And this round SHARPENS what `h3` was**: at the `n = 3`
  corollaries `(3 : F) ≠ 0` now enters only as `((3 : ℕ) : F) ≠ 0`, i.e. purely as the index
  hypothesis, where round 2's docstring said
  *"`h3` is the count and nothing else"*.  The count no longer needs a `3`.  ⚠️ It still does not
  guard the tripling formula, and that is still worth saying:
  `EllipticCurves.Torsion.TriplingSurjective` records in terms that `hasXCoordFormula_three` needs
  no `(3 : F) ≠ 0`.

## Non-vacuity

⚠️ **The hypothesis is `Ψ₃.eval x₀ = 0`, so the fixture has to have a rational `3`-torsion
`x`-coordinate**, and ⚠️ **that is a hypothesis to be supplied and NOT a restriction on which
fixture may be used.**  In particular it does **not** rule out the tripling fixture
`EllipticCurves.Fixture.y2EqX3AddOne` that `EllipticCurves.Torsion.TriplingSurjective`'s own `ℚ`
block runs on.  What that block certifies there is `Φ₃(2) = (−1)·Ψ₃(2)²`, so its `x = 2` is the
**preimage** and its `x₀` is `−1`; the readings `Ψ₃(2) = 72` and `Ψ₂Sq(2) = 36` are at the preimage
and say nothing about the hypothesis here, while the target `x₀ = −1` has `Ψ₃(−1) = 3 − 12 = −9 ≠ 0`
and indeed is not a `3`-torsion `x`-coordinate — it is the `2`-torsion point.  ⚠️ **But the curve is
not excluded, only that `x₀` is**: `y² = x³ + 1` has `b₆ = 4` and `Ψ₃ = 3X⁴ + 12X = 3X(X³ + 4)`, so
`Ψ₃(0) = 0` and `x₀ = 0` would serve on that curve too.  ⚠️ **An earlier round of this file stated
the exclusion of the curve as a fact and it was false**; the fixture below is a choice and not a
forced one.  It is
`EllipticCurves.Fixture.y2AddYEqX3` at `R = ℚ` — `y² + y = x³`, whose `b`-invariants are
`b₂ = b₄ = b₈ = 0` and `b₆ = 1`, so

```
Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈ = 3X⁴ + 3X,        Ψ₃(0) = 0.
```

**Three of the four `n = 3` public statements are certified there, and the fourth cannot be.**
⚠️ **The four general statements get no separate `ℚ` instantiation and do not need one**: at `n = 3`
each corollary's proof term *is* an application of its general form, so the fixture instantiates
both members of every pair at once.  **That is an argument and not an omission, and it is the same
one the closed-field row below makes.**
`separable_Φ_three_sub_C_mul_ΨSq`, `separable_Φ_three_sub_C_mul_Ψ₃_sq` and
`separable_Φ_three_sub_C_mul_ΨSq_of_mem_torsion` each get an instantiation at `(0, 0)`; the last of
the three is the one that matters, being the form a caller holding the point has and the only one
binding an extra instance, and it needs `(0, 0) ∈ (y2AddYEqX3 ℚ).torsion 3`, which is
`memTorsionThree_y2AddYEqX3` and **not** an inference anyone may read off `Ψ₃(0) = 0` in prose.
⚠️ **`separable_Φ_three_sub_C_mul_ΨSq_of_isAlgClosed` gets no fixture-level `example` and is not
vacuous either**: `ℚ` is not algebraically closed, so no fixture over `ℚ` can state it — but it is
what `separable_Φ_three_sub_C_mul_ΨSq` applies over `AlgebraicClosure F`, so
`exampleSeparableTriplingPoly`'s proof term instantiates it at `K = AlgebraicClosure ℚ` on the
base change of this very fixture.  A committed `example` for it would need the
`((y2AddYEqX3 ℚ)⁄AlgClosedQ).IsElliptic` bridge that `EllipticCurves.Fixtures` describes, and buys
nothing the instantiation above does not.

⚠️ **In characteristic `0` the content of `Separable` is squarefreeness and nothing more**, so the
`ℚ` instances certify the statements inhabited rather than informative; the case the theorem is
*for* is `char F = p` with `p` odd and `p ∤ n`, where a squarefree polynomial can still fail to be
separable, and **no fixture in this tree instantiates the statements over such a field.**
⚠️ **The reason is not that the tree has no such field — it has one, and the obstruction is a
different one.**  `EllipticCurves.Fixtures`' inventory of the four finite-field certificates lists
`exampleCurveFive`, `⟨0,0,0,-1,0⟩` over `ZMod 5` (`EllipticCurves.FunctionField.MulByNDegreeTower`),
and `char (ZMod 5) = 5` is odd with `5 ∤ 3`, so `h2`, `h3` and `p ∤ n` are all available there.
What is not available is a root: that curve has `b₂ = b₆ = 0`, `b₄ = -2` and `b₈ = -1`, so
`Ψ₃ = 3X⁴ + 4X² + 4` over `ZMod 5`, and since `x⁴ = 1` for every `x ≠ 0` in `𝔽₅` it takes only the
values `Ψ₃(0) = 4` and `3 + 4x² + 4 ∈ {1, 3}` — ⚠️ **never `0`, so `preΨ₃` has no root in `𝔽₅` and
there is no `x₀` to state any of these at.**  ⚠️ **Widening the index does not widen the
certificate**, and that is stated here rather than left to be inferred from the new statements.
**That limit is stated rather than papered over**, and it is the same shape as
`EllipticCurves.Torsion.HalvingGaloisTower`'s *"certified inhabited and NOT certified
informative"*.

## References

* [Silverman, *The arithmetic of elliptic curves*][silverman2009], III.4 (the multiplication-by-`m`
  map and its division polynomials) and III.6 (torsion).
-/

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-! ### One convenience

⚠️ Both declarations below are `private` and they are one convenience twice over — a total
`x`-coordinate and the `rfl` that reads it at an affine point.  **Neither duplicates anything.**
The root count of a polynomial, which the first round of this file restated verbatim from a
`private` lemma of `EllipticCurves.Torsion.OddTorsionCount`, is **exported** from there and used
below under its own name, `card_root_subtype`.  ⚠️ `#1255` is the precedent and
`eval_Φ_three_ne_zero_of_root_ΨSq` (`EllipticCurves.Torsion.TriplingSurjective`) records it in its
own docstring — of a local `have`, *"which was that lemma restated inside a proof because it was
`private` where it lived; `#1255` made it public and the local copy is gone"*. -/

/-- The `x`-coordinate of a point, with the point at infinity sent to `0`.  ⚠️ The junk value is
never read: every use below is guarded by a proof that the point is affine. -/
private def xCoordOf : W.Point → F
  | .zero => 0
  | .some x _ _ => x

private lemma xCoordOf_some {x y : F} (h : W.Nonsingular x y) :
    xCoordOf (Point.some x y h) = x := rfl

/-! ### The fibre of `[n]` as a coset of `E[n]` -/

section Fibre

variable [DecidableEq F] [W.IsElliptic]

/-- **The fibre of `[n]` over a point in its image is a coset of `E[n]`**, at every `n` and over
every field, from `[W.IsElliptic]` and `[DecidableEq F]` alone.  ⚠️ **Both of those are in scope
from the enclosing `section Fibre` and `[W.IsElliptic]` is genuinely used** — it is what makes
`W.Point` the group this map subtracts in; nothing about elliptic curves *beyond the group law*
enters, since the map is `P ↦ P − P₀` in an abelian group.  It is stated here only because the
counting step below needs it. -/
private noncomputable def fibreEquivTorsion {n : ℕ} {S P₀ : W.Point} (hP₀ : n • P₀ = S) :
    {P : W.Point // n • P = S} ≃ W.torsion n where
  toFun P := ⟨P.1 - P₀, mem_torsion_iff.mpr (by rw [smul_sub, P.2, hP₀, sub_self])⟩
  invFun T := ⟨T.1 + P₀, by rw [smul_add, mem_torsion_iff.mp T.2, zero_add, hP₀]⟩
  left_inv P := Subtype.ext (sub_add_cancel _ _)
  right_inv T := Subtype.ext (add_sub_cancel_right _ _)

end Fibre

/-! ### The count, over an algebraically closed field -/

section AlgClosed

variable [IsAlgClosed F] [W.IsElliptic]

/-- **The tripling polynomial of an `n`-torsion point is separable at every ODD `n`, over an
algebraically closed field** with `(2 : F) ≠ 0` and `(n : F) ≠ 0`.

⚠️ **This is the general-index form, and `separable_Φ_three_sub_C_mul_ΨSq_of_isAlgClosed` below is
now its corollary at `n = 3`.**  Round 2 of this file stated that the index was blocked because
*"`card_torsion_three` has no general-index form anywhere"*; that sentence was false —
`card_torsion_eq_sq` (`EllipticCurves.Torsion.StructureGeneral`) is the general count, at every `n`
with `(2 : F) ≠ 0` and `(n : F) ≠ 0` and with no parity hypothesis — and reaching it is an **import
cost** and not an absence.  It is paid: `## The cost of the general index` in the module docstring
prices it.

The proof is the `n = 3` proof with five inputs replaced by their general forms and **one** tactic
block genuinely new, the parity step:

* `hasXCoordFormula_of_two_ne_zero` for `hasXCoordFormula_three`;
* `nsmul_surjective_of_two_ne_zero` for `exists_nsmul_three_eq`;
* `eval_Φ_ne_zero_of_eval_ΨSq_eq_zero` for `eval_Φ_three_ne_zero_of_root_ΨSq`;
* `ΨSq_natCast_eq_sq_of_odd` at `hodd` rather than at `by decide`;
* `card_torsion_eq_sq` for `card_torsion_three`, which is the one that costs the import.

⚠️ **`Odd n` is where the `n = 3` proof's *"`S = 3S − 2S = 0`"* step becomes a real argument**:
writing `n = 2k + 1`, the opposite-point branch gives `2 • S = 0` and then
`0 = n • S = k • (2 • S) + S = S`, contradicting `S ≠ 0`.  The module docstring called this argument
*"not formalised"*; it is formalised here, in four lines.  ⚠️ **It is NOT the only place parity is
used: `hodd` is consumed at four sites inside this theorem's own proof and pays three distinct
debts** — twice at `nsmul_eq_zero_iff_eval_preΨ_eq_zero`, once at `ΨSq_natCast_eq_sq_of_odd` (both
`EllipticCurves.Torsion.OddTorsionCount`, both *binding* `Odd n`), and once at the `obtain ⟨k, hk⟩`
of the step above.  ⚠️ **And the first two debts are FALSE at even `n` rather than unproved**, by
`WeierstrassCurve.ΨSq_ofNat`'s `if Even n`; `## What is *not* here` says where an even-`n` round
starts instead. -/
theorem separable_Φ_sub_C_mul_ΨSq_of_isAlgClosed_of_odd (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n)
    (hn : (n : F) ≠ 0) {x₀ : F} (hx₀ : (W.preΨ (n : ℤ)).eval x₀ = 0) :
    (W.Φ n - C x₀ * W.ΨSq n).Separable := by
  classical
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨y₀, hy₀⟩ := exists_equation (W := W) h2 x₀
  have hS : W.Nonsingular x₀ y₀ := equation_iff_nonsingular.mp hy₀
  set S : W.Point := Point.some x₀ y₀ hS with hSdef
  have hSne : S ≠ 0 := Point.some_ne_zero hS
  have hSn : n • S = 0 :=
    (nsmul_eq_zero_iff_eval_preΨ_eq_zero h2 hodd hS).mpr hx₀
  set g : F[X] := W.Φ n - C x₀ * W.ΨSq n with hgdef
  have hdeg : g.natDegree = n ^ 2 := natDegree_Φ_sub_C_mul_ΨSq (W := W) hn0 x₀
  have hg0 : g ≠ 0 := fun h => by
    rw [h] at hdeg; exact (pow_ne_zero 2 hn0) (by simpa using hdeg.symm)
  have hsplits : g.Splits := IsAlgClosed.splits g
  have hrc : Multiset.card g.roots = n ^ 2 := by rw [splits_iff_card_roots.mp hsplits, hdeg]
  have hgeval : ∀ x : F, g.eval x = (W.Φ n).eval x - x₀ * (W.ΨSq n).eval x := by
    intro x; rw [hgdef, eval_sub, eval_mul, eval_C]
  -- a root of `g` is not a root of `ΨSqₙ`, because `Φₙ` and `ΨSqₙ` have no common root
  have hne_of_root : ∀ x : F, g.eval x = 0 → (W.ΨSq n).eval x ≠ 0 := by
    intro x hx h0
    refine eval_Φ_ne_zero_of_eval_ΨSq_eq_zero (W := W) h2 hn0 x h0 ?_
    rw [hgeval, h0, mul_zero, sub_zero] at hx
    exact hx
  -- a point of the fibre is affine and its `x`-coordinate is a root of `g`
  have hfwd : ∀ P : W.Point, n • P = S → g.eval (xCoordOf P) = 0 := by
    rintro (_ | ⟨x, y, hns⟩) hP
    · exact absurd (by rw [← hP, show (Point.zero : W.Point) = 0 from rfl, smul_zero]) hSne.symm
    · have hpre : (W.preΨ (n : ℤ)).eval x ≠ 0 := fun h0 =>
        hSne (by rw [← hP, (nsmul_eq_zero_iff_eval_preΨ_eq_zero h2 hodd hns).mpr h0])
      have hΨ : (W.ΨSq n).eval x ≠ 0 := by
        intro h0
        refine hpre ?_
        rw [ΨSq_natCast_eq_sq_of_odd (W := W) hodd, eval_pow] at h0
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
      obtain ⟨y', h', hxy⟩ := hasXCoordFormula_of_two_ne_zero (W := W) h2 n hns hΨ
      rw [hP, hSdef] at hxy
      have hx0 : (W.Φ n).eval x / (W.ΨSq n).eval x = x₀ :=
        (((Point.some.injEq _ _ _ _ _ _).mp hxy).1).symm
      rw [xCoordOf_some, hgeval, ← hx0, div_mul_cancel₀ _ hΨ, sub_self]
  -- the `x`-coordinate is injective on the fibre: `P = −Q` would force `2S = 0`, and `n` is ODD
  have hinj : ∀ P Q : W.Point, n • P = S → n • Q = S →
      xCoordOf P = xCoordOf Q → P = Q := by
    rintro (_ | ⟨x, y, hns⟩) Q hP hQ hxx
    · exact absurd (by rw [← hP, show (Point.zero : W.Point) = 0 from rfl, smul_zero]) hSne.symm
    rcases Q with _ | ⟨x', y', hns'⟩
    · exact absurd (by rw [← hQ, show (Point.zero : W.Point) = 0 from rfl, smul_zero]) hSne.symm
    rw [xCoordOf_some, xCoordOf_some] at hxx
    rcases (Point.X_eq_iff (h₁ := hns) (h₂ := hns')).mp hxx with hc | hc
    · exact hc
    · exfalso
      have hSS : S = -S := by
        nth_rewrite 1 [← hP]
        rw [hc, smul_neg, hQ]
      have h2S : (2 : ℕ) • S = 0 := by
        rw [two_nsmul]
        nth_rewrite 1 [hSS]
        exact neg_add_cancel S
      obtain ⟨k, hk⟩ := hodd
      refine hSne ?_
      have hsplit : n • S = k • ((2 : ℕ) • S) + S := by
        rw [hk, add_nsmul, one_nsmul, mul_nsmul]
      rw [h2S, smul_zero, zero_add] at hsplit
      rw [← hsplit, hSn]
  -- every root of `g` is the `x`-coordinate of a point of the fibre
  have hsurj : ∀ x : F, g.eval x = 0 → ∃ P : W.Point, n • P = S ∧ xCoordOf P = x := by
    intro x hx
    have hΨ := hne_of_root x hx
    obtain ⟨y, hy⟩ := exists_equation (W := W) h2 x
    have hns : W.Nonsingular x y := equation_iff_nonsingular.mp hy
    obtain ⟨y', h', hxy⟩ := hasXCoordFormula_of_two_ne_zero (W := W) h2 n hns hΨ
    have hx0 : (W.Φ n).eval x / (W.ΨSq n).eval x = x₀ := by
      rw [hgeval] at hx
      rw [sub_eq_zero.mp hx, mul_div_assoc, div_self hΨ, mul_one]
    rcases (Point.X_eq_iff (h₁ := h') (h₂ := hS)).mp hx0 with hc | hc
    · exact ⟨Point.some x y hns, by rw [hxy, hc, hSdef], xCoordOf_some hns⟩
    · refine ⟨-Point.some x y hns, ?_, ?_⟩
      · rw [smul_neg, hxy, hc, hSdef, neg_neg]
      · rw [Point.neg_some]; rfl
  -- `n²` points in the fibre, `n²` distinct roots, degree `n²`
  obtain ⟨P₀, hP₀⟩ := nsmul_surjective_of_two_ne_zero (W := W) h2 hn0 S
  have hfib : Nat.card {P : W.Point // n • P = S} = n ^ 2 := by
    rw [Nat.card_congr (fibreEquivTorsion hP₀), card_torsion_eq_sq h2 hn]
  have hbij : Function.Bijective
      (fun P : {P : W.Point // n • P = S} => (⟨xCoordOf P.1, hfwd P.1 P.2⟩ :
        {x : F // g.eval x = 0})) := by
    constructor
    · rintro ⟨P, hP⟩ ⟨Q, hQ⟩ hPQ
      exact Subtype.ext (hinj P Q hP hQ (congrArg Subtype.val hPQ))
    · rintro ⟨x, hx⟩
      obtain ⟨P, hP, hxP⟩ := hsurj x hx
      exact ⟨⟨P, hP⟩, Subtype.ext hxP⟩
  have hrootsn : g.roots.toFinset.card = n ^ 2 := by
    rw [← card_root_subtype hg0, ← Nat.card_congr (Equiv.ofBijective _ hbij), hfib]
  exact (nodup_roots_iff_of_splits hg0 hsplits).mp
    (Multiset.toFinset_card_eq_card_iff_nodup.mp (by rw [hrootsn, hrc]))

/-- **The tripling polynomial of a `3`-torsion point is separable, over an algebraically closed
field** with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`.

⚠️ **This is now a COROLLARY of the general odd-index form above, stated verbatim in the
signature it has always had**, so every consumer is unaffected and the statement this file has
shipped since round 1 is not weakened by a character.  `(3 : F) ≠ 0` enters only as
`((3 : ℕ) : F) ≠ 0`, `Odd 3` is `by decide`, and `preΨ_three` is the bridge from `Ψ₃` to `preΨ 3`.

The mathematics is unchanged and is described at the general form: a bijection between the fibre
`{P : nP = S}` and the root set, `n²` points against `n²` roots against degree `n²`.  At `n = 3`
that is the nine-element fibre and the nine roots the earlier rounds were written around.

⚠️ **The parity step is what the earlier rounds could state only at `3`** — *"`S = 3S − 2S = 0`"* —
and it is the one line of the general proof that is not a name swap. -/
theorem separable_Φ_three_sub_C_mul_ΨSq_of_isAlgClosed (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {x₀ : F} (hx₀ : W.Ψ₃.eval x₀ = 0) : (W.Φ 3 - C x₀ * W.ΨSq 3).Separable := by
  have hpre : (W.preΨ ((3 : ℕ) : ℤ)).eval x₀ = 0 := by
    rw [show ((3 : ℕ) : ℤ) = (3 : ℤ) by norm_num, preΨ_three]; exact hx₀
  simpa using separable_Φ_sub_C_mul_ΨSq_of_isAlgClosed_of_odd (W := W) h2 (n := 3) (by decide)
    (by exact_mod_cast h3) hpre


end AlgClosed

/-! ### The descent to an arbitrary field -/

section General

variable [W.IsElliptic]

/-- **The tripling polynomial of an `n`-torsion point is separable at every ODD `n`, over an
ARBITRARY field** with `(2 : F) ≠ 0` and `(n : F) ≠ 0`.

⚠️ **This is the statement a consumer over a general base wants, and it is now index-free.**
`separable_Φ_three_sub_C_mul_ΨSq` below is its corollary at `n = 3`, in the signature it has always
had.

⚠️ **Neither `[DecidableEq F]` nor `[IsAlgClosed F]` nor a `y`-coordinate is bound.**  The
hypothesis is one polynomial evaluation, `Polynomial.separable_map` moves the conclusion across
`F → AlgebraicClosure F` in both directions, and `WeierstrassCurve.map_Φ`, `map_ΨSq` and
Mathlib's `map_preΨ` move the three objects.  The `n`-torsion *point* exists over the closure and
nowhere is it asked to exist over `F`. -/
theorem separable_Φ_sub_C_mul_ΨSq_of_odd (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n)
    (hn : (n : F) ≠ 0) {x₀ : F} (hx₀ : (W.preΨ (n : ℤ)).eval x₀ = 0) :
    (W.Φ n - C x₀ * W.ΨSq n).Separable := by
  classical
  set K := AlgebraicClosure F with hK
  have h2' : (2 : K) ≠ 0 := fun hzero =>
    h2 ((algebraMap F K).injective (by rw [map_ofNat, map_zero]; exact hzero))
  have hn' : ((n : ℕ) : K) ≠ 0 := fun hzero =>
    hn ((algebraMap F K).injective (by rw [map_natCast, map_zero]; exact hzero))
  have hx0' : ((W⁄K).preΨ (n : ℤ)).eval (algebraMap F K x₀) = 0 := by
    rw [show (W⁄K).preΨ (n : ℤ) = (W.preΨ (n : ℤ)).map (algebraMap F K) from
      WeierstrassCurve.map_preΨ .., eval_map, eval₂_at_apply, hx₀, map_zero]
  rw [← Polynomial.separable_map (algebraMap F K),
    show (W.Φ n - C x₀ * W.ΨSq n).map (algebraMap F K)
      = (W⁄K).Φ n - C (algebraMap F K x₀) * (W⁄K).ΨSq n by
      rw [show (W⁄K).Φ (n : ℤ) = (W.Φ (n : ℤ)).map (algebraMap F K) from WeierstrassCurve.map_Φ ..,
        show (W⁄K).ΨSq (n : ℤ) = (W.ΨSq (n : ℤ)).map (algebraMap F K) from
          WeierstrassCurve.map_ΨSq .., Polynomial.map_sub, Polynomial.map_mul, map_C]]
  exact separable_Φ_sub_C_mul_ΨSq_of_isAlgClosed_of_odd h2' hodd hn' hx0'

/-- **The tripling polynomial of a `3`-torsion point is separable, over an arbitrary field** with
`(2 : F) ≠ 0` and `(3 : F) ≠ 0`.

⚠️ **A corollary of `separable_Φ_sub_C_mul_ΨSq_of_odd` above**, in the signature it has always
had, so every consumer is unaffected.  The base-change argument that used to live here — and the
`map_Ψ₃` it ran on — is now at the general form, against Mathlib's `map_preΨ`; here `preΨ_three`
is the only bridge left.  ⚠️ **Neither `[DecidableEq F]` nor `[IsAlgClosed F]` nor a
`y`-coordinate is bound**, at either index. -/
theorem separable_Φ_three_sub_C_mul_ΨSq (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x₀ : F}
    (hx₀ : W.Ψ₃.eval x₀ = 0) : (W.Φ 3 - C x₀ * W.ΨSq 3).Separable := by
  have hpre : (W.preΨ ((3 : ℕ) : ℤ)).eval x₀ = 0 := by
    rw [show ((3 : ℕ) : ℤ) = (3 : ℤ) by norm_num, preΨ_three]; exact hx₀
  simpa using separable_Φ_sub_C_mul_ΨSq_of_odd (W := W) h2 (n := 3) (by decide)
    (by exact_mod_cast h3) hpre

/-- **`Φₙ − C x₀ · preΨₙ²` is separable at every odd `n`** — the same statement as
`separable_Φ_sub_C_mul_ΨSq_of_odd`, in the spelling that carries the square explicitly.
`ΨSq_natCast_eq_sq_of_odd` (`EllipticCurves.Torsion.OddTorsionCount`) is the whole proof, and it is
where `Odd n` pays a second time: at even `n` the `Ψ₂Sq` factor is present and the two spellings
come apart. -/
theorem separable_Φ_sub_C_mul_preΨ_sq_of_odd (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n)
    (hn : (n : F) ≠ 0) {x₀ : F} (hx₀ : (W.preΨ (n : ℤ)).eval x₀ = 0) :
    (W.Φ n - C x₀ * W.preΨ (n : ℤ) ^ 2).Separable := by
  have h := separable_Φ_sub_C_mul_ΨSq_of_odd (W := W) h2 hodd hn hx₀
  rwa [ΨSq_natCast_eq_sq_of_odd (W := W) hodd] at h

/-- **`Φₙ − C x₀ · ΨSqₙ` is separable at the `x`-coordinate of an affine `n`-torsion point**, at
every odd `n` — the root hypothesis of `separable_Φ_sub_C_mul_ΨSq_of_odd` supplied from membership
of `W.torsion n`, which is the form a caller holding the point has.

⚠️ This and its `n = 3` corollary are the only **theorems** in this file that bind
`[DecidableEq F]`, and they bind it because `W.torsion` does.  ⚠️ **Theorems and not
declarations**: the `private def` `fibreEquivTorsion` binds it too, from the `variable` line of
its enclosing `section Fibre`. -/
theorem separable_Φ_sub_C_mul_ΨSq_of_mem_torsion_of_odd [DecidableEq F] (h2 : (2 : F) ≠ 0)
    {n : ℕ} (hodd : Odd n) (hn : (n : F) ≠ 0) {x₀ y₀ : F} (hS : W.Nonsingular x₀ y₀)
    (hSn : Point.some x₀ y₀ hS ∈ W.torsion n) : (W.Φ n - C x₀ * W.ΨSq n).Separable :=
  separable_Φ_sub_C_mul_ΨSq_of_odd h2 hodd hn
    ((nsmul_eq_zero_iff_eval_preΨ_eq_zero h2 hodd hS).mp (mem_torsion_iff.mp hSn))

/-- **`Φ₃ − C x₀ · Ψ₃²` is separable** — the same statement as
`separable_Φ_three_sub_C_mul_ΨSq`, in the spelling
`exists_nsmul_three_eq_some_of_root` (`EllipticCurves.Torsion.TriplingSurjective`) states its own
root hypothesis in.  `WeierstrassCurve.ΨSq_three` is the whole proof. -/
theorem separable_Φ_three_sub_C_mul_Ψ₃_sq (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x₀ : F}
    (hx₀ : W.Ψ₃.eval x₀ = 0) : (W.Φ 3 - C x₀ * W.Ψ₃ ^ 2).Separable := by
  have h := separable_Φ_three_sub_C_mul_ΨSq h2 h3 hx₀
  rwa [WeierstrassCurve.ΨSq_three] at h

/-- **`Φ₃ − C x₀ · ΨSq₃` is separable at the `x`-coordinate of an affine `3`-torsion point** — the
root hypothesis of `separable_Φ_three_sub_C_mul_ΨSq` supplied from membership of `W.torsion 3`,
which is the form a caller holding the point has.

⚠️ **A corollary of `separable_Φ_sub_C_mul_ΨSq_of_mem_torsion_of_odd` above**, in the signature it
has always had.  It and that general form are the only two **theorems** in this file that bind
`[DecidableEq F]`, and they bind it because `W.torsion` does — the `private def`
`fibreEquivTorsion` binds it as well, which is why the unit here is the theorem. -/
theorem separable_Φ_three_sub_C_mul_ΨSq_of_mem_torsion [DecidableEq F] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {x₀ y₀ : F} (hS : W.Nonsingular x₀ y₀)
    (hS3 : Point.some x₀ y₀ hS ∈ W.torsion 3) : (W.Φ 3 - C x₀ * W.ΨSq 3).Separable := by
  simpa using separable_Φ_sub_C_mul_ΨSq_of_mem_torsion_of_odd (W := W) h2 (n := 3) (by decide)
    (by exact_mod_cast h3) hS (by simpa using hS3)

end General

/-! ### Non-vacuity over `ℚ`

`EllipticCurves.Fixture.y2AddYEqX3` at `R = ℚ`, whose `3`-torsion point `(0, 0)` puts a rational
root at `x₀ = 0`.  ⚠️ **Three of the four `n = 3` public statements above are instantiated here**
and the fourth, the closed-field form, cannot be over `ℚ`; the module docstring's `## Non-vacuity`
says which and why.  ⚠️ **The torsion membership of `(0, 0)` is proved and not asserted** — a root
of `Ψ₃` is not by itself a torsion point until `nsmul_eq_zero_iff_eval_preΨ_eq_zero` is applied. -/

section Nonvacuity

open EllipticCurves.Fixture

/-- **`Ψ₃ = 3X⁴ + 3X` on `y² + y = x³`**, from `b₂ = b₄ = b₈ = 0` and `b₆ = 1`. -/
private lemma Ψ₃_y2AddYEqX3 : (y2AddYEqX3 ℚ).Ψ₃ = 3 * X ^ 4 + 3 * X := by
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, y2AddYEqX3]
  norm_num

/-- **`0` is a root of `Ψ₃` on `y² + y = x³`**, so `(0, 0)` is a `3`-torsion point of it. -/
private lemma eval_Ψ₃_zero_y2AddYEqX3 : (y2AddYEqX3 ℚ).Ψ₃.eval 0 = 0 := by
  rw [Ψ₃_y2AddYEqX3]; simp

/-- ⚠️ **`x₀` is not a root of its own tripling polynomial, and here the value is `1`.**  The
structural reason is in the module docstring — a root of `Φ₃ − C x₀·ΨSq₃` is not a root of `Ψ₃`,
while `x₀` is one — and this is that reason exhibited rather than asserted.  It is the statement
`3S ≠ S`, read off the polynomials. -/
private lemma eval_triplingPoly_zero_y2AddYEqX3 :
    ((y2AddYEqX3 ℚ).Φ 3 - C (0 : ℚ) * (y2AddYEqX3 ℚ).ΨSq 3).eval 0 = 1 := by
  rw [eval_sub, eval_mul, eval_C, Φ_three_eval]
  simp only [preΨ₄_eval, WeierstrassCurve.Ψ₃, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, y2AddYEqX3]
  norm_num

/-- **The tripling polynomial of `(0, 0)` on `y² + y = x³` over `ℚ` is separable** — the headline,
inhabited.  ⚠️ **Certified inhabited and not certified informative**: `ℚ` has characteristic `0`, so
`Separable` and `Squarefree` agree there and the statement's own reason for existing — the
characteristic-`p` case, `p > 3` — is not exercised by any fixture in this tree. -/
private theorem exampleSeparableTriplingPoly :
    ((y2AddYEqX3 ℚ).Φ 3 - C (0 : ℚ) * (y2AddYEqX3 ℚ).ΨSq 3).Separable :=
  separable_Φ_three_sub_C_mul_ΨSq (by norm_num) (by norm_num) eval_Ψ₃_zero_y2AddYEqX3

/-- **`Φ₃ − C 0 · Ψ₃²` is separable on the same fixture** — `separable_Φ_three_sub_C_mul_Ψ₃_sq`
inhabited.  One line, and it is here only because the `ΨSq 3`-versus-`Ψ₃ ^ 2` spelling is the whole
content of that statement. -/
private theorem exampleSeparableTriplingPolyΨ₃Sq :
    ((y2AddYEqX3 ℚ).Φ 3 - C (0 : ℚ) * (y2AddYEqX3 ℚ).Ψ₃ ^ 2).Separable :=
  separable_Φ_three_sub_C_mul_Ψ₃_sq (by norm_num) (by norm_num) eval_Ψ₃_zero_y2AddYEqX3

/-- **`(0, 0)` lies on `y² + y = x³`**: `0 + 0 = 0`. -/
private lemma equation_y2AddYEqX3_zero : (y2AddYEqX3 ℚ).Equation 0 0 := by
  rw [Affine.equation_iff]; norm_num [y2AddYEqX3]

/-- **`(0, 0)` is a `3`-torsion point of `y² + y = x³` over `ℚ`.**

⚠️ **This is the inference the module docstring's `Ψ₃(0) = 0` does not by itself make**, and it is
here rather than in prose for that reason: `nsmul_eq_zero_iff_eval_preΨ_eq_zero`
(`EllipticCurves.Torsion.OddTorsionCount`) is what turns the root into the torsion membership, and
it needs `(2 : ℚ) ≠ 0` and oddness of `3`. -/
private lemma memTorsionThree_y2AddYEqX3 :
    Point.some 0 0 (equation_iff_nonsingular.mp equation_y2AddYEqX3_zero) ∈
      (y2AddYEqX3 ℚ).torsion 3 := by
  rw [mem_torsion_iff]
  refine (nsmul_eq_zero_iff_eval_preΨ_eq_zero (by norm_num) (n := 3) (by decide)
    (equation_iff_nonsingular.mp equation_y2AddYEqX3_zero)).mpr ?_
  rw [show ((3 : ℕ) : ℤ) = (3 : ℤ) by norm_num, preΨ_three]
  exact eval_Ψ₃_zero_y2AddYEqX3

/-- **`separable_Φ_three_sub_C_mul_ΨSq_of_mem_torsion` inhabited**, at `(0, 0)` on `y² + y = x³`
over `ℚ`.  ⚠️ **This is the public statement that most needed a certificate**: it is the form a
caller holding the point has, and it is the only one of the four binding an extra instance
(`[DecidableEq F]`, from `W.torsion`). -/
private theorem exampleSeparableTriplingPolyOfMemTorsion :
    ((y2AddYEqX3 ℚ).Φ 3 - C (0 : ℚ) * (y2AddYEqX3 ℚ).ΨSq 3).Separable :=
  separable_Φ_three_sub_C_mul_ΨSq_of_mem_torsion (by norm_num) (by norm_num)
    (equation_iff_nonsingular.mp equation_y2AddYEqX3_zero) memTorsionThree_y2AddYEqX3

end Nonvacuity

end WeierstrassCurve.Affine
