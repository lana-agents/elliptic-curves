/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.ThreeTorsion
import Mathlib.Algebra.Field.ZMod

/-!
# `#E[3] ≤ 3` in characteristic `3`: the `n = 3` descent route is not undecided there, it is false

`EllipticCurves.Torsion.ThreeTorsionStructure` computes `#E[3] = 9` over an algebraically closed
field with `(2 : F) ≠ 0` and `(3 : F) ≠ 0` (`card_torsion_three`), and
`EllipticCurves.Torsion.ThreeTorsion` bounds `#E[3] ≤ 9` under `(3 : F) ≠ 0` alone
(`card_torsion_three_le`).  ⚠️ **This file shows the `(3 : F) ≠ 0` in both is NECESSARY and not
inherited decoration**: in characteristic `3` the count is at most `3`, so `#E[3] = 9` is **false**
there rather than unproved, and the `n = 3` descent's counting input does not merely lack a proof.

The `n = 2` mirror at the other prime is `#2228`, and this file follows its shape deliberately: one
polynomial identity over a `CommRing`, one `[W.IsElliptic]`-only input, one sharp statement about
pairs of points, two counts, one exact triviality on the degenerate branch, and a certificate.

## The degeneration

`Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈`, and in characteristic `3` the three coefficients carrying a
`3` vanish outright, leaving

```
Ψ₃ = b₂X³ + b₈       (`Ψ₃_eq_of_char_three`).
```

⚠️ **The tree already asserted this twice in prose and nowhere as a theorem** —
`EllipticCurves.Torsion.ThreeTorsion`'s module docstring and
`EllipticCurves.Torsion.TriplingSurjective`'s, the latter in terms (*"In characteristic `3` the
polynomial `Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈` degenerates to `b₂X³ + b₈`"*).  It is stated here
over an arbitrary `[CommRing R]`: it is an identity in the `b`-invariants and binds no field and no
ellipticity.

## Why the count drops from `9` to `3`, in one sentence per branch

`Ψ₃` cuts out the `x`-coordinates of the nonzero `3`-torsion points
(`mem_torsion_three_some_iff`, which carries **no** characteristic hypothesis), and the counting
engine of `EllipticCurves.Torsion.Finite` puts at most two points above each such `x`, plus `O`.
⚠️ **So the whole question is how many roots `b₂X³ + b₈` has, and the answer is AT MOST ONE in both
branches** — whence `#E[3] ≤ 2 · 1 + 1 = 3` against the `2 · 4 + 1 = 9` of the generic case.

* **`b₂ ≠ 0` (ordinary).**  `b₂x³ + b₈ = 0` says `x³ = −b₈/b₂`, and `x ↦ x³` is **injective** in
  characteristic `3`, because `(x − x')³ = x³ − x'³` there.  ⚠️ **One root at most, and the proof
  does NOT factor `Ψ₃` as `b₂(X + c)³`** — that needs a cube root of `b₈/b₂` inside `F`, and the
  field is not assumed perfect; over `𝔽₃(t)` it need not exist.  The injection is written out as
  one `linear_combination` (`eq_of_pow_three_eq_of_char_three`); no `CharP` instance and no
  `frobenius` appears.
* **`b₂ = 0` (supersingular).**  Then `Ψ₃ = C b₈` is a **nonzero constant**, so it has no root at
  all and `E[3]` is trivial — an equality and not a bound
  (`torsion_three_eq_bot_of_b₂_eq_zero_of_char_three`).

## ⚠️ The third branch, which the `n = 2` mirror does not have, and it is EMPTY

`Ψ₃ ≡ 0` — that is, `b₂ = b₈ = 0` — would break the argument outright, since then *every* `x` is a
root and no bound follows.  ⚠️ **It cannot happen, and `[W.IsElliptic]` is what rules it out.**  In
characteristic `3`, `b₈ = b₂b₆ − b₄²`, so at `b₂ = 0` one has `b₈ = −b₄²`, and `b₈ = 0` then forces
`b₄ = 0`; but `Δ = −b₂²b₈ − 8b₄³` there, which at `b₂ = b₄ = 0` is `0`, contradicting
`[W.IsElliptic]`.  This is `b₈_ne_zero_of_b₂_eq_zero_of_char_three`, and it is simultaneously the
supersingular branch's only input and the reason the third branch is vacuous — ⚠️ **so it is stated
once and used twice, rather than split.**

⚠️ **`[W.IsElliptic]` is therefore necessary and not decoration**, exactly as at `n = 2`, where
`a₁ = a₃ = 0` makes `Ψ₂Sq` the zero polynomial.  It is the *only* hypothesis on `W` beyond the
characteristic that any statement below binds.

## Main statements

**14** public theorems.  ⚠️ `#print axioms` over all fourteen reaches **0** `sorryAx` and nothing
outside `{propext, Classical.choice, Quot.sound}`; ⚠️ **two of the fourteen —
`b₈_eq_of_char_three` and `Δ_eq_of_char_three` — return only `{propext, Quot.sound}`**, `ring`
needing no choice.

⚠️ **The instance census, read off `#check` through `lake env lean` and not off the `variable`
lines**: `[W.IsElliptic]` reaches **ten** of the fourteen, `[DecidableEq F]` reaches **five**, and
`[Field F]` reaches **eleven** — the three exceptions being the `section CommRing` block.  **Four**
of the fourteen carry neither `[W.IsElliptic]` nor `[DecidableEq F]`, and ⚠️ **one of those four,
`eq_of_pow_three_eq_of_char_three`, mentions no curve at all**: it is a statement about a field, and
it is flagged as such on its bullet.  Each bullet below names the binders it lacks.

* `WeierstrassCurve.Affine.Ψ₃_eq_of_char_three` — `Ψ₃ = b₂X³ + b₈`, ⚠️ **over an arbitrary
  `[CommRing R]` and not only over a field**, which is where Mathlib's `Ψ₃` lives.  ⚠️ **No
  `[Field]`, no `[W.IsElliptic]`, no `[DecidableEq]`.**
* `WeierstrassCurve.Affine.b₈_eq_of_char_three` — `b₈ = b₂b₆ − b₄²`.  ⚠️ **No `[Field]`, no
  `[W.IsElliptic]`.**
* `WeierstrassCurve.Affine.Δ_eq_of_char_three` — `Δ = −b₂²b₈ − 8b₄³`.  ⚠️ **No `[Field]`, no
  `[W.IsElliptic]`.**  ⚠️ These two are **binder-form transcriptions of Mathlib's
  `WeierstrassCurve.b_relation_of_char_three` and `WeierstrassCurve.Δ_of_char_three`** and are not
  new mathematics; see `## On the spelling of the hypothesis` for why the transcription is here at
  all and what it costs (one `linear_combination` each).
* `WeierstrassCurve.Affine.eq_of_pow_three_eq_of_char_three` — cubing is injective.  ⚠️ **No `W`,
  no `[W.IsElliptic]`, no `[DecidableEq F]`**: it is about `F` alone, and it is the one statement in
  this file that a reader looking for curve content should skip.
* `WeierstrassCurve.Affine.b₈_ne_zero_of_b₂_eq_zero_of_char_three` — `b₂ = 0 → b₈ ≠ 0`, from
  `[W.IsElliptic]` alone.  ⚠️ **No `[DecidableEq F]`.**  The supersingular branch's only input, and
  the emptiness of the third branch.
* `WeierstrassCurve.Affine.eq_of_Ψ₃_eval_eq_zero_of_char_three` — **`Ψ₃` has at most one root in
  characteristic `3`.**  ⚠️ **No `[DecidableEq F]`.**  This is the polynomial content of the whole
  file; both branches are discharged inside it, which is why nothing downstream case-splits.
* `WeierstrassCurve.Affine.subsingleton_setOf_Ψ₃_root_of_char_three`,
  `WeierstrassCurve.Affine.finite_setOf_Ψ₃_root_of_char_three`,
  `WeierstrassCurve.Affine.ncard_setOf_Ψ₃_root_le_one_of_char_three` — the root set as a
  `Subsingleton`, as `Finite` and with `ncard ≤ 1`.  ⚠️ **No `[DecidableEq F]` on any of these.**
  ⚠️ **The finiteness here does NOT come from `Ψ₃ ≠ 0`** — the route
  `EllipticCurves.Torsion.ThreeTorsion` uses, which is unavailable because `Ψ₃_ne_zero` binds
  `(3 : R) ≠ 0` — but from the subsingleton, which is stronger and needs no degree argument.
* `WeierstrassCurve.Affine.x_eq_of_mem_torsion_three_of_char_three` — **any two nonzero
  `3`-torsion points share an `x`-coordinate.**  The sharp statement of this file; the two counts
  below are corollaries.  ⚠️ At `n = 2` the mirror is an equality of *points*
  (`#2228`'s `eq_of_mem_torsion_two_of_char_two`); here it is only an equality of `x`-coordinates,
  and that is not a weakness of the proof — the `ZMod 3` certificate below exhibits **two** distinct
  nonzero `3`-torsion points over one `x`.
* `WeierstrassCurve.Affine.finite_torsion_three_of_char_three` — `E[3]` is finite.  ⚠️ **This is
  not available from `finite_torsion_three`**, which binds `(3 : F) ≠ 0`, so in characteristic `3`
  the finiteness of `E[3]` is proved here for the first time.
* `WeierstrassCurve.Affine.card_torsion_three_le_three_of_char_three` — **`#E[3] ≤ 3`**, over any
  field of characteristic `3`, algebraically closed or not.
* `WeierstrassCurve.Affine.card_torsion_three_ne_nine_of_char_three` — **`#E[3] ≠ 9`**, the form a
  reader of the characteristic-`3` hedges is looking for and the one the `#962` descent needs.
* `WeierstrassCurve.Affine.torsion_three_eq_bot_of_b₂_eq_zero_of_char_three` — when `b₂ = 0`,
  `E[3]` is **trivial**, not merely small.  ⚠️ This is exact rather than a bound, and it needs no
  **perfectness** and no `[IsAlgClosed F]`; it does bind `[Field F]`, `[DecidableEq F]` and
  `[W.IsElliptic]` like every other statement in `section Torsion`.

## ⚠️ What is *not* here

* **`#E[3] = 3` when `b₂ ≠ 0`.**  ⚠️ **It is FALSE over a general field of characteristic `3`, and
  the bound above is sharp for that reason.**  The argument produces *at most* one `x`; it does not
  produce one, because `x³ = −b₈/b₂` needs a cube root in `F` and `x ↦ x³` is injective but **not
  surjective** on a non-perfect field — over `𝔽₃(t)` it is not.  Even granted the `x`, the `y`
  solves a quadratic that need not split, and the torsion criterion additionally wants
  `2y + a₁x + a₃ ≠ 0`, i.e. `y ≠ a₁x + a₃` in characteristic `3`, which is not automatic either.
  ⚠️ **So two independent existence questions sit between `≤ 3` and `= 3`, where `#2228` at `n = 2`
  had one**, and this file states neither because nothing in this tree consumes them.  The bound is
  attained — see `## Non-vacuity` — so `≤ 3` cannot be improved.
* **Characteristic `2` at `n = 3`, and this is the half of the swept sentence that is NOT decided
  here.**  ⚠️ `3` is prime to `2`, so `#E[3] = 9` is **true** in characteristic `2` exactly as in
  characteristic `0` and there is no falsity theorem to write.  What blocks `n = 3` there is the
  `(2 : F) ≠ 0` of the tangent slope's denominator, which
  `EllipticCurves.Torsion.TriplingSurjective` records in terms; that is a **formalisation** gap and
  not an obstruction, and no sentence in this file or in the two it sweeps may be read as closing
  it.
* **Any theory of the Frobenius, of inseparability of `[3]` as an isogeny, or of
  supersingularity.**  The words *ordinary* and *supersingular* appear above only to name the two
  branches of one `b₂ = 0` case split — and in characteristic `3`, `c₄ = b₂²`
  (`WeierstrassCurve.c₄_of_char_three`), so `b₂ = 0` is precisely `j = 0`, which is what makes those
  the right names.  ⚠️ **The case split is on `b₂` and NOT on `a₁`**, unlike `#2228`'s; in
  characteristic `3`, `b₂ = a₁² + a₂`.  Nothing below imports a theory to state a count.
* **`hprin` in characteristic `3`, and any statement about `mulByThreeEndo` or the tripling
  tower.**  Once `#E[3] ≠ 9` is a theorem the descent's `hcard` input is known false there and the
  question does not arise, which is the whole point.  **No such statement is owed and none made.**
* **Separability of `Ψ₃` in characteristic `3`.**  ⚠️ **Deliberately not stated, and the reason is
  `#2228`'s round-2 defect**: on the `b₂ = 0` branch `Ψ₃` is a nonzero **constant**, hence a unit of
  `F[X]`, hence separable, while on the `b₂ ≠ 0` branch it is `b₂(X³ + b₈/b₂)` with derivative
  `3X² = 0`, hence *not* separable.  **The row goes opposite ways in the two branches**, so
  *"`Ψ₃` degenerates, hence it is inseparable"* is a false inference, exactly as *"`Ψ₂Sq` is a
  square, hence inseparable"* was.  Deciding it is a separate statement, not a residue of this
  one.

## On the spelling of the hypothesis

⚠️ **`(3 : F) = 0` and `[CharP F 3]` are not interchangeable in a binder**, and this file uses the
first throughout.  The reason is symmetry with what it contradicts: every statement it is about —
`card_torsion_three`, `card_torsion_three_of_splits`, `card_torsion_three_le`, `card_torsion_eq_sq`
— binds `(3 : F) ≠ 0` as an explicit hypothesis, so `(3 : F) = 0` is the literal negation and a
reader can put the two side by side.  `EllipticCurves.Torsion.XSupport` is the tree's only `CharP`
consumer and it converts through `CharP.cast_eq_zero_iff`; the same conversion is available to any
caller that holds `[CharP F 3]` instead.

⚠️ **Mathlib's characteristic-`3` `b`- and `Δ`-relations are `[CharP R 3]`-gated, so the two this
file needs are transcribed rather than imported**, and the transcription is **one
`linear_combination` each** — `b₈_eq_of_char_three` and `Δ_eq_of_char_three` above, which are
Mathlib's `b_relation_of_char_three` and `Δ_of_char_three` with the instance replaced by the
hypothesis and the same proof term.  ⚠️ **No `Fact (Nat.Prime 3)` is needed and none is declared**;
the alternative — deriving `CharP F 3` from `(3 : F) = 0` — costs a primality fact and a
`Nontrivial`, which the `CommRing` section does not have and does not want.

## Non-vacuity

⚠️ **Both branches are certified over `ZMod 3`, and the two conclusions are DIFFERENT**, which is
what makes the `b₂` case split real rather than a proof convenience:

* `y² = x³ − x`, i.e. `⟨0, 0, 0, -1, 0⟩` — `b₂ = 0`, the **supersingular** branch.  `b₄ = −2 = 1`
  and `b₈ = −a₄² = −1 = 2 ≠ 0`, so `Ψ₃ = 2` is a nonzero constant, `E[3] = ⊥` **exactly**, and
  `#E[3] = 1`.
* `y² = x³ + x² − 1`, i.e. `⟨0, 1, 0, 0, -1⟩` — `b₂ = 4 = 1 ≠ 0`, the **ordinary** branch.
  `Ψ₃ = X³ + 2`, whose unique root is `x = 1`, and `y² = 1` there gives the two points `(1, 1)` and
  `(1, 2)`.  ⚠️ **So `E[3] ≠ ⊥` and `#E[3] = 3` exactly, which certifies that the bound `≤ 3` is
  ATTAINED** and that `torsion_three_eq_bot_of_b₂_eq_zero_of_char_three` is genuinely about the
  `b₂ = 0` branch and not about characteristic `3`.
* ⚠️ **The two points also witness why the sharp statement above is about `x`-coordinates and not
  about points**: `(1, 1) ≠ (1, 2)` are both nonzero and both `3`-torsion.

⚠️ **NEITHER CURVE IS TAKEN FROM `EllipticCurves.Fixtures`, AND THE REASON IS A MEASURED PRICE AND
NOT AN ABSENCE.**  `EllipticCurves.Fixture.y2EqX3SubX` **is** `⟨0, 0, 0, -1, 0⟩`, so the
supersingular curve is literally that fixture's tuple.  ⚠️ **But `EllipticCurves.Fixtures` is not
in `EllipticCurves.Torsion.ThreeTorsion`'s import closure** — unlike
`EllipticCurves.Torsion.TwoTorsion`'s, which is why `#2228` could reuse a fixture and this file
cannot — and the edge costs **+31 modules over all packages** (`+1` in `EllipticCurves`, namely
`Fixtures` itself) for a five-integer tuple, **measured at `88a5e00`**.  Two `private def`s are
cheaper than `+31` modules, and the ordinary curve is in no fixture at any rate.  ⚠️ **No
`Fact (Nat.Prime 3)` is declared here either**: `Field (ZMod 3)` synthesises from this file's two
imports alone.

Both `IsElliptic` instances are proved by the tree's standard finite-field recipe —
`isElliptic_iff`, `isUnit_iff_ne_zero`, `decide +kernel` — the one-line recipe the finite-field
rows `EllipticCurves.Fixtures` deliberately does not serve are each built by, of which `Fixtures`
itself records only the last step (*"prove `IsElliptic` by `decide +kernel`"*), and which
`Fixtures`' own instances cannot supply here because they are stated over a field where the
discriminant is a `norm_num` fact.  `Δ = 64 = 1` on the first curve and `Δ = −368 = 1` on the
second, both in `ZMod 3`.

⚠️ **The RECIPE is what is quoted above; the COUNT standing beside it in `Fixtures` deliberately is
not, because this file is two rows of the population that count is over** — the two
`private instance`s below extend the very list a numeral quoted here would stand on, which is how
the quotation this paragraph used to carry came to cite a census its own commit falsified.
⚠️ **And that count is SHAPE-DEPENDENT, so it must never be quoted without its shape**: the
CERTIFICATE reading (`private instance : _.IsElliptic := by … decide +kernel` at a finite base) and
the CURVE-DEFINITION reading (`private … : Affine … := ⟨…⟩`, grouped by resolved finite base)
return populations at `52d6dea` that are **not the same population** — only the first reaches
`EllipticCurves.Torsion.TwoTorsionCharTwo`'s `y2AddYEqX3 (ZMod 2)` instance, and only the second
reaches `EllipticCurves.Torsion.TriplingSurjective`'s `curveChar2`, which carries no `IsElliptic`
instance at all.  ⚠️ **Nor does the second reading have one size until the generic-base fixtures
are ruled on**: `TwoTorsionCharTwo`'s `curveOrdinaryCharTwo`, declared
over a generic base — `R` a type variable — and instantiated at `ZMod 2`, is a
`private … : Affine … := ⟨…⟩` whose base its own signature does not name — and the first reading
cannot reach it under any relaxation, its ellipticity being `isElliptic_curveOrdinaryCharTwo`, a
`private theorem` off a hand `Δ`, not an instance closed by `decide +kernel`.  ⚠️ **So a size here
would need a reading AND a base-resolution rule named beside it**, which is why this file
publishes none.  `#2264` owns the repair of `Fixtures`' clause itself.  ⚠️ **Both declarations are
cited by NAME and not by line on purpose** — the approved-and-queued PR #834 displaces
`curveOrdinaryCharTwo` and its theorem within `TwoTorsionCharTwo` without RENAMING either, so a
line address written here would rot the moment that branch lands.

## ⚠️ One Mathlib import beyond `ThreeTorsion`, and it is the certificate's and not the theory's

`Mathlib.Algebra.Field.ZMod` is imported for **`Field (ZMod 3)`** alone.  ⚠️ **Nothing in the theory
above needs it** — every public statement is over an abstract `[CommRing R]` or `[Field F]` and
would compile against `EllipticCurves.Torsion.ThreeTorsion` alone — and ⚠️ **it is nearly free**:
`+1` module over all packages and `+0` in `EllipticCurves`, its whole closure already lying inside
`ThreeTorsion`'s, **measured at `88a5e00`**.  This file's `EllipticCurves` closure is the **3**
modules it publishes — `Torsion.{Defs, Finite, ThreeTorsion}` — also **measured at `88a5e00`**.

## The sweep, and what it deliberately leaves alone

Two files are re-worded by the commit that adds this one, and ⚠️ **the two are re-worded in
DIFFERENT ways, because the two kinds of clause are different**: a claim about a file's own reach
takes a **pointer** in place, and only a claim about the **tree** is split or retired.
`### Reach clauses` is the rule; the discriminator is the clause's subject and not its wording.

⚠️ **THE SEED THE OBVIOUS RECOGNISER GIVES CANNOT SEE THE MORE IMPORTANT OF THE TWO SITES.**
``grep -rn 'characteristic `3`' --include=*.lean`` over `EllipticCurves/` returns **13** hits in
**7** files at `88a5e00`, identical under `-i` — and **0** of them in
`EllipticCurves.Torsion.ThreeDivisionField`, whose bullet is the first site this commit splits: it
writes *"Characteristic `2` or `3`"*, so the word is capitalised **and** the `3` is four tokens away
from it, and the seed misses it at both flags.  ⚠️ **The recogniser that finds it is
``Characteristic `2` or `3` ``, which returns 2 hits in 2 files at `88a5e00`** — and the second of
those two is named below as deliberately unswept.  ⚠️ **Publish the DELTA and re-derive the
absolute ends**: the delta is a property of this commit's diff and does not move when `main` does,
and both ends at both flags are in the commit message.

* **`EllipticCurves.Torsion.ThreeTorsion`** — ⚠️ **its clauses are NOT re-worded; the file gains a
  pointer section and nothing else.**  There are **6** hits of ``[Aa]way from characteristic `3` ``
  in it at `88a5e00`, and **every one is a claim about its own reach**, which stays true of it — so
  `### Reach clauses`' *"false or merely partial"* test returns **partial** and a pointer is what
  they take.  ⚠️ **This module is genuinely UPSTREAM of this one, so the pointer's
  *"downstream of this file"* is an import-closure FACT and not a guess**: this file imports it, and
  `ThreeTorsion` is in this module's closure while this module is in none of `ThreeTorsion`'s.
* **`EllipticCurves.Torsion.ThreeDivisionField`** — ⚠️ **this one IS split, because its clause is
  about the tree**: *"nothing below decides anything in either characteristic"* is now half false.
  The bullet becomes two, the characteristic-`3` half gaining the reason and ⚠️ **the
  characteristic-`2` half kept intact and unweakened, with an explicit note that this theorem does
  not decide it.**  That module is **import-incomparable** with this one — neither is in the other's
  import closure, in either direction — so the `import` line there is declined on a price and not
  blocked by a cycle: the edge would add **one** module to its `EllipticCurves` closure (9 → 10) and
  **two** over all packages, this module itself and `Mathlib.Algebra.Field.ZMod`, **measured at
  `88a5e00`**.  ⚠️ **A docstring pointer is not an import edge**, and at that price declining it is
  a cost judgement about a sentence of prose.  The vocabulary is that of
  `EllipticCurves.Torsion.DoublingCoords`, which writes **import-incomparable** twice of sibling
  modules in this same directory.
* ⚠️ **`EllipticCurves.Torsion.TriplingGaloisTower`:`## What is not here` carries the OTHER
  *"Characteristic `2` or `3`"* bullet and is deliberately NOT swept** — named here so the next
  round need not rediscover it.  The discriminator is sharp: that bullet is a **hypothesis
  inventory** of its own statements (*"Every statement that uses the tripling polynomial's
  separability carries both `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, inherited from `TriplingSeparable`"*)
  and it makes **no decidability claim about the tree at all**, which is the clause
  `ThreeDivisionField`'s bullet added and this one did not.  ⚠️ **Same wording, different subject,
  different disposition.**
* ⚠️ **`EllipticCurves.Torsion.TriplingSurjective` is NOT swept either, and it is the site a
  widening sweep would take first.**  Its characteristic-`3` clause says that *its own* theorems
  **hold** there — *"every statement below still holds"* — which is true, already argued, and not a
  hedge.
* ⚠️ **Nor are the four remaining seed sites**, and each for a reason of its own:
  `EllipticCurves.Torsion.ThreeTorsionStructure` describes its own proof's use of `deg Ψ₃ = 4`;
  `EllipticCurves.Torsion.NsmulSurjective` records that `nsmul_three_surjective` **holds** in
  characteristic `3`; `EllipticCurves.FunctionField.MulByNComposition` and
  `EllipticCurves.FunctionField.MulByNPlaceComposition` likewise report presence rather than
  absence; and `EllipticCurves.FunctionField.WeilPairingAlternatingTwoRational`'s clause is about
  `n = 2` and a spurious `(3 : F) ≠ 0`, which this theorem does not touch.  **A sweep that widens
  past what the theorem covers is the defect this work exists to remove, not to reproduce.**

## References

* [Silverman, *The arithmetic of elliptic curves*][silverman2009], III.2 (the description of `E[n]`
  by the division polynomials), III.6 Corollary 6.4 (the bound `#E[n] ≤ n²`) and V.3 (the two
  characteristic-`p` branches of `E[p]`).
-/

open Polynomial

namespace WeierstrassCurve.Affine

/-! ### The `3`-division polynomial degenerates to a cubic in `X³`

⚠️ **This one section is over `[CommRing R]`**, because `Ψ₃` and the `b`-invariants are and the
three identities below need nothing else; every later section is over `[Field F]`. -/

section CommRing

variable {R : Type*} [CommRing R] {W : Affine R}

/-- **`Ψ₃ = b₂X³ + b₈` in characteristic `3`.**

`Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈` loses its quartic, quadratic and linear terms outright, and
nothing else happens: the two surviving coefficients are untouched.

⚠️ **The tree asserted this twice in prose before it was a theorem** — see
`EllipticCurves.Torsion.ThreeTorsion`'s module docstring and
`EllipticCurves.Torsion.TriplingSurjective`'s, the latter in exactly these terms.

⚠️ **Nothing here is about fields.**  `Ψ₃` is Mathlib's, stated over a `CommRing`, and the proof is
one `linear_combination` in the `b`-invariants, so the statement is too; the `[Field F]` form every
consumer below wants is a direct instance.  In particular this does **not** bind `[W.IsElliptic]`,
which the degenerate case `b₂ = b₈ = 0` needs but this identity does not. -/
theorem Ψ₃_eq_of_char_three (h3 : (3 : R) = 0) :
    W.Ψ₃ = C W.b₂ * X ^ 3 + C W.b₈ := by
  have h3' : (3 : R[X]) = 0 := by
    rw [← map_ofNat (C : R →+* R[X]) 3, h3, map_zero]
  rw [WeierstrassCurve.Ψ₃]
  linear_combination (X ^ 4 + C W.b₄ * X ^ 2 + C W.b₆ * X) * h3'

/-- **`b₈ = b₂b₆ − b₄²` in characteristic `3`.**

⚠️ **A binder-form transcription of Mathlib's `WeierstrassCurve.b_relation_of_char_three`**, whose
`[CharP R 3]` this file does not want; the proof term is Mathlib's own with the instance replaced by
the hypothesis.  See `## On the spelling of the hypothesis` in the module docstring. -/
theorem b₈_eq_of_char_three (h3 : (3 : R) = 0) : W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 := by
  linear_combination W.b_relation - W.b₈ * h3

/-- **`Δ = −b₂²b₈ − 8b₄³` in characteristic `3`.**

⚠️ **A binder-form transcription of Mathlib's `WeierstrassCurve.Δ_of_char_three`**, on the same
terms as `b₈_eq_of_char_three` above.  Together the two are the whole input to
`b₈_ne_zero_of_b₂_eq_zero_of_char_three`, which is the only place either is used. -/
theorem Δ_eq_of_char_three (h3 : (3 : R) = 0) : W.Δ = -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 := by
  rw [WeierstrassCurve.Δ]
  linear_combination (-9 * W.b₆ ^ 2 + 3 * W.b₂ * W.b₄ * W.b₆) * h3

end CommRing

/-! ### Cubing is injective, and an elliptic curve with `b₂ = 0` has `b₈ ≠ 0` -/

variable {F : Type*} [Field F] {W : Affine F}

/-- **Cubing is injective in characteristic `3`**, because `(x − x')³ = x³ − x'³` there.

⚠️ **This is Frobenius injectivity written out** rather than invoked: no `CharP` instance, no
`frobenius` and no perfect-field hypothesis appears, only `3 = 0` inside a `linear_combination`.

⚠️ **It mentions no curve**, and it is the one statement in this file that a reader looking for
curve content should skip.  ⚠️ **Injective is all that is claimed**: `x ↦ x³` is *not* surjective on
a non-perfect field, which is exactly why the module docstring's `## ⚠️ What is *not* here` refuses
`#E[3] = 3` on the ordinary branch. -/
theorem eq_of_pow_three_eq_of_char_three (h3 : (3 : F) = 0) {x x' : F}
    (h : x ^ 3 = x' ^ 3) : x = x' := by
  have hs : (x - x') ^ 3 = 0 := by
    linear_combination h + (-x ^ 2 * x' + x * x' ^ 2) * h3
  exact sub_eq_zero.mp (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp hs)

/-- **In characteristic `3` an elliptic curve with `b₂ = 0` has `b₈ ≠ 0`.**

At `b₂ = 0` the relation `b₈ = b₂b₆ − b₄²` reads `b₈ = −b₄²`, so `b₈ = 0` forces `b₄ = 0`; and
`Δ = −b₂²b₈ − 8b₄³` then vanishes, contradicting `[W.IsElliptic]`.

⚠️ **This one statement does two jobs and is deliberately not split**: it is the supersingular
branch's only input — it makes `Ψ₃ = C b₈` a *nonzero* constant, hence root-free — and it is also
what rules out the degenerate third branch `Ψ₃ ≡ 0`, which would otherwise make every `x` a root and
leave no bound at all.  `#2228` has no such branch, because at `n = 2` the two coefficients of
`Ψ₂Sq = (a₁X + a₃)²` are squares of `a`-invariants rather than `b`-invariants.

`[W.IsElliptic]` is necessary and not decoration: at `b₂ = b₄ = 0` in characteristic `3` the
polynomial `Ψ₃` is `0`. -/
theorem b₈_ne_zero_of_b₂_eq_zero_of_char_three [W.IsElliptic] (h3 : (3 : F) = 0)
    (hb₂ : W.b₂ = 0) : W.b₈ ≠ 0 := by
  intro hb₈
  have hb₄ : W.b₄ = 0 := by
    have hrel := b₈_eq_of_char_three (W := W) h3
    rw [hb₂, hb₈, zero_mul] at hrel
    have : W.b₄ ^ 2 = 0 := by linear_combination hrel
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  refine (‹W.IsElliptic›.isUnit).ne_zero ?_
  rw [Δ_eq_of_char_three (W := W) h3, hb₂, hb₄]
  ring

/-! ### `Ψ₃` has at most one root -/

/-- **`Ψ₃` has at most one root in characteristic `3`.**

The polynomial content of this file, and both branches are discharged inside it, which is why
nothing downstream case-splits:

* `b₂ = 0` — then `b₂x³ + b₈ = 0` reads `b₈ = 0`, refused by
  `b₈_ne_zero_of_b₂_eq_zero_of_char_three`, so there is **no** root and the conclusion is vacuous;
* `b₂ ≠ 0` — then `b₂x³ = −b₈ = b₂x'³`, and cancelling `b₂` and applying
  `eq_of_pow_three_eq_of_char_three` gives `x = x'`.

⚠️ **Note what is *not* used: no degree argument, no `Ψ₃ ≠ 0`, and no factorisation of `Ψ₃` as
`b₂(X + c)³`** — that last would need a cube root of `b₈/b₂` inside `F`, which a non-perfect field
need not have.  Against the generic case's *four* roots, this `1` is the whole reason the count
drops from `9` to `3`. -/
theorem eq_of_Ψ₃_eval_eq_zero_of_char_three [W.IsElliptic] (h3 : (3 : F) = 0) {x x' : F}
    (hx : W.Ψ₃.eval x = 0) (hx' : W.Ψ₃.eval x' = 0) : x = x' := by
  rw [Ψ₃_eq_of_char_three h3] at hx hx'
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X] at hx hx'
  rcases eq_or_ne W.b₂ 0 with hb₂ | hb₂
  · rw [hb₂, zero_mul, zero_add] at hx
    exact absurd hx (b₈_ne_zero_of_b₂_eq_zero_of_char_three h3 hb₂)
  · exact eq_of_pow_three_eq_of_char_three h3
      (mul_left_cancel₀ hb₂ (by linear_combination hx - hx'))

variable (W) in
/-- In characteristic `3` the root set of `Ψ₃` is a subsingleton. -/
theorem subsingleton_setOf_Ψ₃_root_of_char_three [W.IsElliptic] (h3 : (3 : F) = 0) :
    {x : F | W.Ψ₃.eval x = 0}.Subsingleton :=
  fun _ hx _ hx' => eq_of_Ψ₃_eval_eq_zero_of_char_three h3 hx hx'

variable (W) in
/-- In characteristic `3` the root set of `Ψ₃` is finite.

⚠️ **This does NOT come from `Ψ₃ ≠ 0`**, the route `EllipticCurves.Torsion.finite_setOf_Ψ₃_root`
takes, which is unavailable here because `Ψ₃_ne_zero` binds `(3 : R) ≠ 0`.  It comes from the
subsingleton above, which is a stronger fact and needs no degree argument. -/
theorem finite_setOf_Ψ₃_root_of_char_three [W.IsElliptic] (h3 : (3 : F) = 0) :
    {x : F | W.Ψ₃.eval x = 0}.Finite :=
  (W.subsingleton_setOf_Ψ₃_root_of_char_three h3).finite

variable (W) in
/-- In characteristic `3` the root set of `Ψ₃` has at most **one** element — against the **four** of
`EllipticCurves.Torsion.ncard_setOf_Ψ₃_root_le`, which binds `(3 : F) ≠ 0`.  This is the cell the
counting engine consumes. -/
theorem ncard_setOf_Ψ₃_root_le_one_of_char_three [W.IsElliptic] (h3 : (3 : F) = 0) :
    {x : F | W.Ψ₃.eval x = 0}.ncard ≤ 1 :=
  (Set.ncard_le_one (W.finite_setOf_Ψ₃_root_of_char_three h3)).mpr
    fun _ ha _ hb => W.subsingleton_setOf_Ψ₃_root_of_char_three h3 ha hb

/-! ### `E[3]` sits over a single `x`-coordinate, so `#E[3] ≤ 3` -/

section Torsion

variable [DecidableEq F] [W.IsElliptic]

/-- **Any two nonzero `3`-torsion points of a curve in characteristic `3` share an
`x`-coordinate.**

The sharp statement of this file; both counts below are corollaries of it through the counting
engine of `EllipticCurves.Torsion.Finite`.

⚠️ **The conclusion is an equality of `x`-coordinates and NOT of points**, unlike `#2228`'s
`eq_of_mem_torsion_two_of_char_two` at `n = 2`, and that is not slack in the proof: over `ZMod 3`
the curve `y² = x³ + x² − 1` carries the two distinct nonzero `3`-torsion points `(1, 1)` and
`(1, 2)` above the single root `x = 1`, so the points really can differ.  The `n = 2` mirror is an
equality of points only because a `2`-torsion point is fixed by negation, so its `y` is
determined. -/
theorem x_eq_of_mem_torsion_three_of_char_three (h3 : (3 : F) = 0) {x y x' y' : F}
    {h : W.Nonsingular x y} {h' : W.Nonsingular x' y'}
    (hP : Point.some x y h ∈ W.torsion 3) (hQ : Point.some x' y' h' ∈ W.torsion 3) :
    x = x' :=
  eq_of_Ψ₃_eval_eq_zero_of_char_three h3 (Ψ₃_eval_eq_zero_of_mem_torsion_three hP)
    (Ψ₃_eval_eq_zero_of_mem_torsion_three hQ)

variable (W) in
/-- **`E[3]` is finite in characteristic `3`.**

⚠️ **This is not available from `EllipticCurves.Torsion.finite_torsion_three`**, which binds
`(3 : F) ≠ 0`, so in characteristic `3` the finiteness of `E[3]` is proved here for the first time —
and it comes out of the subsingleton root set rather than out of a degree bound. -/
theorem finite_torsion_three_of_char_three (h3 : (3 : F) = 0) : Finite (W.torsion 3) :=
  W.finite_torsion_of_xCoords (W.finite_setOf_Ψ₃_root_of_char_three h3)
    fun _ _ _ hP => Ψ₃_eval_eq_zero_of_mem_torsion_three hP

variable (W) in
/-- **`#E[3] ≤ 3` over any field of characteristic `3`**, algebraically closed or not.

`Ψ₃` has at most one root, the counting engine puts at most two points above it, and `O` is the
third.  ⚠️ Against `EllipticCurves.Torsion.card_torsion_three_le`'s `2 · 4 + 1 = 9` under
`(3 : F) ≠ 0`, this is `2 · 1 + 1 = 3`.

⚠️ **The bound is attained and is not an equality.**  The `ZMod 3` certificate below reaches `3` on
the ordinary branch and `1` on the supersingular one; over a non-perfect field of characteristic `3`
the ordinary branch can be smaller still, for the two independent existence reasons the module
docstring's `## ⚠️ What is *not* here` states. -/
theorem card_torsion_three_le_three_of_char_three (h3 : (3 : F) = 0) :
    Nat.card (W.torsion 3) ≤ 3 :=
  (W.card_torsion_le_of_xCoords (W.finite_setOf_Ψ₃_root_of_char_three h3)
      fun _ _ _ hP => Ψ₃_eval_eq_zero_of_mem_torsion_three hP).trans <| by
    have := W.ncard_setOf_Ψ₃_root_le_one_of_char_three h3
    omega

variable (W) in
/-- **`#E[3] ≠ 9` in characteristic `3`.**

⚠️ **This is the statement the `(3 : F) ≠ 0` hypotheses of `card_torsion_three` and
`card_torsion_three_of_splits` (`EllipticCurves.Torsion.ThreeTorsionStructure`),
`card_torsion_three_le` (`EllipticCurves.Torsion.ThreeTorsion`) and `card_torsion_eq_sq`
(`EllipticCurves.Torsion.StructureGeneral`, at `n = 3`) exist for**, and it says that those
hypotheses are necessary rather than inherited decoration.  It is also the form a reader of the
tree's characteristic-`3` hedges is looking for, and the one the `#962` descent consumes: with
`#E[3] = 9` false, the `hcard` input of the `n = 3` route is false and the question does not
arise. -/
theorem card_torsion_three_ne_nine_of_char_three (h3 : (3 : F) = 0) :
    Nat.card (W.torsion 3) ≠ 9 := by
  intro h
  have := W.card_torsion_three_le_three_of_char_three h3
  omega

/-- **`E[3]` is trivial when `b₂ = 0`**, in characteristic `3` — the supersingular branch, and the
one of the two that is exact over every field.

There `Ψ₃ = C b₈` with `b₈ ≠ 0` by `b₈_ne_zero_of_b₂_eq_zero_of_char_three`, so no affine point has
its `x`-coordinate among the roots of `Ψ₃` and none is `3`-torsion at all.

⚠️ **This is exact rather than a bound, and it needs no perfectness and no `[IsAlgClosed F]`** — it
does bind `[Field F]`, `[DecidableEq F]` and `[W.IsElliptic]`, like every statement in this section.
⚠️ **And it is about the `b₂ = 0` BRANCH and not about characteristic `3`**: the certificate below
exhibits a characteristic-`3` curve with `b₂ ≠ 0` whose `E[3]` has three elements. -/
theorem torsion_three_eq_bot_of_b₂_eq_zero_of_char_three (h3 : (3 : F) = 0) (hb₂ : W.b₂ = 0) :
    W.torsion 3 = ⊥ := by
  refine eq_bot_iff.mpr fun P hP => ?_
  rcases P with _ | ⟨x, y, h⟩
  · exact AddSubgroup.mem_bot.mpr rfl
  · refine absurd ?_ (b₈_ne_zero_of_b₂_eq_zero_of_char_three h3 hb₂)
    have hx := Ψ₃_eval_eq_zero_of_mem_torsion_three hP
    rw [Ψ₃_eq_of_char_three h3] at hx
    simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X, hb₂, zero_mul, zero_add] at hx
    exact hx

end Torsion

/-! ### Non-vacuity over `ZMod 3`, on both branches

`y² = x³ − x` has `b₂ = 0` and `E[3] = ⊥`; `y² = x³ + x² − 1` has `b₂ ≠ 0` and `#E[3] = 3`.
⚠️ **The two conclusions differ, which is what makes the `b₂` case split real.**  ⚠️ **No
`Fact (Nat.Prime 3)` is declared** — `Field (ZMod 3)` synthesises from this file's two imports alone
— and neither curve is drawn from `EllipticCurves.Fixtures`, for the measured reason the module
docstring's `## Non-vacuity` gives. -/

section Nonvacuity

/-- The supersingular characteristic-`3` certificate curve: `y² = x³ − x` over `ZMod 3`. -/
private def curveSS : Affine (ZMod 3) := ⟨0, 0, 0, -1, 0⟩

private instance : (curveSS).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  decide +kernel

private theorem exampleTorsionThreeBot : (curveSS).torsion 3 = ⊥ :=
  torsion_three_eq_bot_of_b₂_eq_zero_of_char_three (by decide) (by decide)

private theorem exampleCardTorsionThree : Nat.card ((curveSS).torsion 3) = 1 := by
  rw [exampleTorsionThreeBot]; simp

private theorem exampleCardTorsionThreeNeNine : Nat.card ((curveSS).torsion 3) ≠ 9 :=
  curveSS.card_torsion_three_ne_nine_of_char_three (by decide)

/-- The ordinary characteristic-`3` certificate curve: `y² = x³ + x² − 1` over `ZMod 3`. -/
private def curveOrd : Affine (ZMod 3) := ⟨0, 1, 0, 0, -1⟩

private instance : (curveOrd).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  decide +kernel

private theorem exampleEquationOrd : (curveOrd).Equation 1 1 :=
  (equation_iff _ _).mpr (by decide)

private theorem exampleNonsingularOrd : (curveOrd).Nonsingular 1 1 :=
  equation_iff_nonsingular.mp exampleEquationOrd

private theorem exampleNegYOrd : (1 : ZMod 3) ≠ (curveOrd).negY 1 1 := by decide

private theorem exampleMemTorsionThreeOrd :
    (Point.some 1 1 exampleNonsingularOrd : (curveOrd).Point) ∈ (curveOrd).torsion 3 := by
  refine (mem_torsion_three_some_iff exampleNegYOrd).mpr ?_
  rw [Ψ₃_eq_of_char_three (by decide)]
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
  decide

private theorem exampleTorsionThreeNeBot : (curveOrd).torsion 3 ≠ ⊥ := by
  intro h
  have := h ▸ exampleMemTorsionThreeOrd
  rw [AddSubgroup.mem_bot] at this
  exact Point.some_ne_zero exampleNonsingularOrd this

private theorem exampleEquationOrd' : (curveOrd).Equation 1 2 :=
  (equation_iff _ _).mpr (by decide)

private theorem exampleNonsingularOrd' : (curveOrd).Nonsingular 1 2 :=
  equation_iff_nonsingular.mp exampleEquationOrd'

private theorem exampleNegYOrd' : (2 : ZMod 3) ≠ (curveOrd).negY 1 2 := by decide

private theorem exampleMemTorsionThreeOrd' :
    (Point.some 1 2 exampleNonsingularOrd' : (curveOrd).Point) ∈ (curveOrd).torsion 3 := by
  refine (mem_torsion_three_some_iff exampleNegYOrd').mpr ?_
  rw [Ψ₃_eq_of_char_three (by decide)]
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
  decide

private theorem exampleCardTorsionThreeOrd : Nat.card ((curveOrd).torsion 3) = 3 := by
  have hfin := curveOrd.finite_torsion_three_of_char_three (by decide)
  have hle := curveOrd.card_torsion_three_le_three_of_char_three (by decide)
  refine le_antisymm hle ?_
  have hinj : Function.Injective (fun i : Fin 3 => (⟨![(0 : (curveOrd).Point),
      Point.some 1 1 exampleNonsingularOrd, Point.some 1 2 exampleNonsingularOrd'] i, by
    fin_cases i
    · exact zero_mem _
    · exact exampleMemTorsionThreeOrd
    · exact exampleMemTorsionThreeOrd'⟩ : (curveOrd).torsion 3)) := by
    intro i j hij
    rw [Subtype.mk.injEq] at hij
    fin_cases i <;> fin_cases j <;> revert hij <;> simp +decide
  calc (3 : ℕ) = Nat.card (Fin 3) := by simp
    _ ≤ Nat.card ((curveOrd).torsion 3) := Nat.card_le_card_of_injective _ hinj

end Nonvacuity

end WeierstrassCurve.Affine
