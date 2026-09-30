/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.PullbackPrincipalityN
import EllipticCurves.FunctionField.PullbackPrincipalityTwoRationalTorsion

/-!
# The Galois package of `[n]∗` at a rational `E[n]`, at every `n` with `(n : F) ≠ 0`

`EllipticCurves.FunctionField.TranslationActionN` and `EllipticCurves.FunctionField.MulByNGalois`
build the Galois package of `F(W) / [n]∗F(W)` at every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`
over an **algebraically closed** base field — **eleven** statements, the `_of_ne_zero` family:
`card_torsionNMul_of_ne_zero` and `finite_torsionNMul_of_ne_zero` in the first file, and
`finrank_fixedFieldN_of_ne_zero`, `fixedFieldN_eq_mulByNFieldRange_of_ne_zero`,
`fixedPoints_subfield_eq_mulByNEndoFieldRange_of_ne_zero`, `normal_mulByNFieldRange_of_ne_zero`,
`isSeparable_mulByNFieldRange_of_ne_zero`, `isGalois_mulByNFieldRange_of_ne_zero` and the three
`Subfield` forms of the last three in the second.  **This file is that package with
`[IsAlgClosed F]` deleted and the count taken as a hypothesis instead**,

* `hcard : Nat.card (W.torsion n) = n ^ 2`, i.e. `E[n] ⊆ E(F)`,

and adds the positivity rungs of the uncollapsed fundamental identity, which need neither, and the
fibre bound they buy.

## ⚠️ The reading of the headline claim, named — because two readings come apart

Two different sentences can be said about the eleven `_of_ne_zero` statements named above, and only
one of them is true:

* ✅ **REPLACEABILITY**, and it is what this file proves: *in every one of them, `[IsAlgClosed F]`
  can be replaced by `hcard`*.  The proof of that claim is the eleven `_of_card` forms below, each
  of which compiles with no closure anywhere in its binder list.
* ⚠️ **ROUTING**, and it must not be read off the above: *every closure-carrying proof of one of
  those conclusions passes through the count*.  That is **false**, and the witness is in this
  tree: `isSeparable_mulByNFieldRange_of_smooth`
  (`EllipticCurves.FunctionField.MulByNSeparable`) proves the same conclusion at a `3`-smooth index
  by a `2^a · 3^b` **induction** whose closure enters through
  `isSeparable_mulByTwoFieldRange_of_isAlgClosed` and
  `isSeparable_mulByThreeFieldRange_of_isAlgClosed` — through no count at all.
  `MulByNGalois`'s own docstring says so in terms at
  `isSeparable_mulByNFieldRange_of_ne_zero`, and the sentence is quoted whole because its tail is
  the reason: *"This is the one place where the general package is not merely the `3`-smooth proof
  with a substituted input, and it is worth saying why."*

⚠️ **Round 1 of this file stated the routing reading over the `3`-smooth family, and it was false
there for exactly that declaration.**  What is claimed here is replaceability, over the
`_of_ne_zero` family — and against *that* family the per-declaration proofs do match, which is
stated below with the **four** exceptions named rather than as a clean universal:

* each of the eleven is its `_of_ne_zero` sibling's proof with **every `_of_ne_zero` input swapped
  for its `_of_card` form**, in the same order and with nothing reordered;
* ⚠️ the exception at the base is `card_torsionNMul_of_card`, where the swap is
  `card_torsion_eq_sq h2 hn` → `by convert hcard` — that being the one step the closure lived in,
  so there is no `_of_card` input to swap for;
* ⚠️ and **two** of the eleven — `normal_mulByNFieldRange_of_card` and
  `isSeparable_mulByNFieldRange_of_card` — carry one line their siblings do not,
  `have hn0 : n ≠ 0 := by rintro rfl; simp at hn`, because `finite_torsionNMul_of_card` binds
  `n ≠ 0` where `finite_torsionNMul_of_ne_zero` derives it internally.  The sandwich's sibling
  already carries that line, so it is **two** additions across the file and not three;
* ⚠️ and the fourth is `finite_torsionNMul_of_card` itself, whose proof is its sibling's **minus**
  that same line — `finite_torsionNMul_of_ne_zero` (`TranslationActionN`) opens with it and this one
  binds `hn` instead.  ⚠️ **It is the cause of the two additions above and is therefore easy to
  count as one of them rather than as a deviation of its own**, which is exactly what the earlier
  wording of this list did: a subtraction departs from *"in the same order and with nothing
  reordered"* exactly as much as an addition does.

This is `#2217`, the general-`n` form of the two existing middle rungs
(`PullbackPrincipalityTwoRationalTorsion`, `#1339`, and `PullbackPrincipalityThreeRationalTorsion`,
`#2215`).  ⚠️ **It does NOT discharge `#2217`**: what lands here is the Galois package, the
positivity pair and the fibre bound; the fibre *description*, `ramificationIdxN_eq_one` at a
rational point, the class computation, the two headlines and the `Recovery` section of `#907` are
named in `## What is *not* here` and are not attempted.  ⚠️ **Nothing here should be reported as
closing `#962`**, whose rows are `n = 2` and `n = 3` and are reached without this file.

## ⚠️ Why every `n` with `(n : F) ≠ 0`, and not `3`-smooth `n`

⚠️ **Round 1 of this file restricted six of its statements to `3`-smooth `n` and said the
restriction *"cannot be dropped"*.  Both halves of that were false and the correction is the
substance of round 2.**  It reached for `finrank_mulByNFieldRange_of_smooth`
(`EllipticCurves.FunctionField.MulByNComposition`), which binds
`hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3`, and called it the only closure-free
`[F(W) : [n]∗F(W)] = n²` in the tree.  It is not, and it is not even the one its own siblings use:

* `finrank_mulByNFieldRange_eq_sq_of_two_ne_zero`
  (`EllipticCurves.FunctionField.MulByNDegreeGeneral`) is the same conclusion at **every** index
  with `((n : ℤ) : F) ≠ 0`, binding no `(3 : F) ≠ 0`, no `n ≠ 0` and no `hfac`.  That file's title
  is *"`[F(W) : [n]∗F(W)] = n²` at general `n`, with no hypothesis left"*.
* `finrank_mulByNEndoFieldRange_of_ne_zero` (`EllipticCurves.FunctionField.MulByNInertia`) is its
  `Subfield` form, whose docstring reads *"**No `[IsAlgClosed F]`, no separability and no
  smoothness.**"*

⚠️ **A claim that a hypothesis cannot be dropped is a claim about the whole tree and not about the
lemma one reached for**, and this tree ships `_of_smooth` beside `_of_ne_zero` systematically —
`finrank_mulByNEndoFieldRange_of_smooth` and `…_of_ne_zero` are 212 lines apart in one file.  The
test is a `grep` for the **conclusion shape**, not for the lemma name.  Nothing is lost by the
correction: `## Recovery` below derives the `3`-smooth signatures from the general ones, and the
`n = 5` certificates there reach an index the retired scope could not.

## Main statements

**23** named declarations — **17** public theorems in four groups, and **6** `private` helpers,
two of them in `## Recovery` and four in the `ℚ` block — plus **6** anonymous `example`s, three of
them the recovery certificates and three the `n = 5` non-vacuity rows.  ⚠️ `#print axioms` over
all seventeen public statements reaches **0** `sorryAx` and nothing outside
`{propext, Classical.choice, Quot.sound}`, all seventeen returning all three.

Every one of the seventeen carries `{F : Type*} [Field F] {W : Affine F}`,
`[IsDedekindDomain W.CoordinateRing]`, `[DecidableEq F]` and `[W.IsElliptic]` from the ambient
`variable` block, with the unused ones `omit`ted per declaration as the two existing rungs do:
`[IsDedekindDomain W.CoordinateRing]` on all **eleven** of the Galois package, `[W.IsElliptic]`
with it on the first two, and `[DecidableEq F]` on the two positivity rungs and the fibre bound.
⚠️ **The three fibre statements of the fourth group `omit` NOTHING, and they are the only public
declarations here that do not** — each of the four is genuinely used, checked by the unused-section
-variable linter on a warning-free build and, for `[DecidableEq F]`, by an `omit` that Lean refuses
with *"cannot omit referenced section variable"*.  ⚠️ **So the clause that used to close this
paragraph — *"Every public declaration in this file `omit`s at least one of the four, and none
omits more than two"* — is re-keyed rather than retired: it is exact of the fourteen it was written
about and false of the seventeen.**

The explicit-hypothesis census over the seventeen, which is what
`## Why every n with (n : F) ≠ 0` costs out:

| binder | statements binding it, of 17 |
|---|---|
| `hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3` | ⚠️ **0** (round 1: **3** of 8) |
| `h3 : (3 : F) ≠ 0` | ⚠️ **0** (round 1: **3** of 8) |
| `hcard : Nat.card (W.torsion n) = n ^ 2` | 14 |
| `h : Transcendental F (n • genericPoint).xCoord` | 14 |
| `h2 : (2 : F) ≠ 0` | 12 |
| `hn : (n : F) ≠ 0` | 9 |
| `hsep` | 4 |
| `hn : ((n : ℤ) : F) ≠ 0` | ⚠️ **3**, all in the fourth group |
| `hP : n • P = S` | ⚠️ **3**, all in the fourth group |
| `hn : n ≠ 0` | 2 |

⚠️ **The maximum moved from `4` back to `7` and that is a fact about the fourth group and not a
regression in the first three.**  It used to read *"the maximum is `4`, where round 1's maximum was
`6`"*, exact over the fourteen.  `ramificationIdxN_eq_one_of_card` binds seven — `h2`, `hn`, `h`,
`hsep`, `hcard`, `hP` and the fibre-membership `hp` — and its `n = 2` counterpart
`ramificationIdxTwo_eq_one_of_card` binds **five** of those seven, lacking only `hn` and `h`, which
are exactly what a general index costs.  ⚠️ **Every one of the first three groups still binds at
most `4`.**

The Galois package at `hcard`, each the `_of_ne_zero` statement of the same name with
`[IsAlgClosed F]` replaced by `hcard`:

* `card_torsionNMul_of_card` — `|E[n]| = n²` in the multiplicative packaging.  ⚠️ **No hypothesis
  on `n` and none on `F`**: it is `hcard` read through `Multiplicative`.
* `finite_torsionNMul_of_card` — finiteness, which is where `n` is first constrained, because
  `n² ≠ 0` is what rules out `Nat.card = 0`.
* `finrank_fixedFieldN_of_card` — Artin's theorem, `[F(W) : Fixed(E[n])] = n²`.
* `fixedFieldN_eq_mulByNFieldRange_of_card` — **the sandwich, and the mathematical content of the
  file**: both outer degrees are `n²`, the inner inclusion is `mulByNEndo_mem_fixedPoints`, and
  `IntermediateField.eq_of_le_of_finrank_eq'` closes it.  ⚠️ The **prime** is load-bearing for the
  reason `MulByNGalois` records at the merged form.
* `fixedPoints_subfield_eq_mulByNEndoFieldRange_of_card` — the same sandwich at the `Subfield`
  level, `SetLike.ext` off the headline.
* `normal_mulByNFieldRange_of_card` / `isSeparable_mulByNFieldRange_of_card` /
  `isGalois_mulByNFieldRange_of_card` — the Galois package in the `IntermediateField`
  presentation, all three read off the **same** fixed field.
* `normal_mulByNEndoFieldRange_of_card` / `isSeparable_mulByNEndoFieldRange_of_card` /
  `isGalois_mulByNEndoFieldRange_of_card` — the same in the `Subfield` presentation, carried
  across `mulByNFieldRangeEquivSubfield` (`#1219`).  ⚠️ **The separability of the three is the one
  a fibre count consumes**, and it is what keeps `hsep` off the headlines a later round states.

The two positivity rungs, which need **neither** `hcard` nor any hypothesis on `n` beyond the
non-constancy of `[n]`:

* `residueDegreeN_pos` — `f_p > 0` at **every** place, not only at those over a named `q`.
* `one_le_ramificationIdxN_mul_residueDegreeN` — every summand of the uncollapsed identity is at
  least `1`.

And what those two buy, once separability is available closure-free:

* `card_fibre_comapProjPointN_le_sq_of_isSeparable` — **at most `n²` places over any place, over
  an arbitrary field**.  `card_fibre_comapProjPointN_le_sq_of_ne_zero`
  (`EllipticCurves.FunctionField.MulByNFibre`) is this bound over `F̄`, where it comes from the
  **collapsed** `∑ e_p = n²`; here it comes from the uncollapsed `∑ e_p · f_p = n²`
  (`sum_ramificationIdxN_mul_residueDegreeN_of_isSeparable_of_ne_zero`,
  `EllipticCurves.FunctionField.MulByNInertia`) against the summand bound.  This is the general-`n`
  form of `card_fibre_comapProjPointTwo_le_four_of_isSeparable`.

And the fibre description that bound buys once a **halving point** is available, which is `#2292`'s
rung and the fourth group.  All three take `hP : n • P = S` and **no surjectivity**:

* `card_fibre_comapProjPointN_projPointOfPoint_of_card` — **the fibre over a rational point has
  exactly `n²` elements**, over an arbitrary field.  `≤` is the bound above; `≥` is the coset
  `{ P ⊕ R : R ∈ E[n] }`.
* `fibre_comapProjPointN_eq_range_of_card` — **the fibre *is* that coset**.  ⚠️ This is the
  declaration `## What is *not* here` used to record as unavailable closure-free.
* `ramificationIdxN_eq_one_of_card` — **`e_p = 1` over a rational point**, read off the
  *uncollapsed* identity, where `MulByNFibre`'s merged form reads it off the collapsed one and is
  `F̄`-only for that reason.

⚠️ **These are the general-`n` forms of `card_fibre_comapProjPointTwo_projPointOfPoint_of_card`,
`fibre_comapProjPointTwo_eq_range_of_card` and `ramificationIdxTwo_eq_one_of_card`
(`PullbackPrincipalityTwoRationalTorsion`), whose hypothesis shape they copy exactly** — that file
has carried `hP` rather than surjectivity since it was written, and `#2292`'s route-1 measurement
is in the end the observation that the general index may copy it.

## ⚠️ Three things `#2217` asked to be measured, measured — and one of them corrects the filing

**1. `pullbackDivisorN_single_eq_sum_torsion_of_ne_zero` really is inside `section IsAlgClosed`,
and the line numbers reproduce.**  At `ac800b3` the section of
`EllipticCurves.FunctionField.MulByNFibre` opens at `:777` with `variable [IsAlgClosed F]` at `:779`
and closes at `:1439`, and that theorem is declared at `:1223` — inside it, with no closure in its
own binder list.  ⚠️ **A binder list is not a hypothesis list**, and the general-`n` fibre
*description* is therefore not available closure-free, which is why it is a later round and not a
specialisation of finished work.  ⚠️ The **bound** is a different statement and does lift; it is in
this file.

⚠️ **AND THE CLOSURE ENTERS THAT SECTION THREE TIMES AND NOT TWICE.**  `MulByNFibre`'s own header
for its fibre section reads

> ⚠️ `[IsAlgClosed F]` enters twice in this section, independently: once so that every place is
> rational and `∑ e_p · f_p` collapses to `∑ e_p` (`sum_ramificationIdxN_of_smooth`), and once so
> that `[n]` is surjective on points (`nsmul_surjective_of_smooth`) and the coset exists at all.
> Neither use is removable by progress on the other.

⚠️ **Read off the four `_of_ne_zero` proofs rather than off that header, there is a third use and it
is the torsion count** — and the same file says so ONE section later, of its own general layer:

> **Right**: none of `#293`'s count, `#1213`'s degree, `#268` or `hprin` (`#962`) is a gate.  The
> general proof consumes the count only in the *fibre* statements, exactly where the `3`-smooth ones
> consume `card_torsion_eq_sq_of_smooth`, and the contraction itself consumes none of the four.

⚠️ **So `MulByNFibre` carries the right account and the wrong count, `80` lines and ONE section
heading apart** — its `:772` against its `:852`, across the single heading between them at `:824`,
its ten section headings standing at `:12 :315 :394 :743 :770 :824 :1079 :1246 :1308 :1320`.
⚠️ **The figure is keyed to blob `173a37980d42fd364a3a33558fc5bb0f660e40f3`, which is that file's
content at every base this one has had**, so a reader can re-take it without needing the `main` it
was read at.
The second passage is about the *contraction*, where *"not the count"* is true, and the first is a
count over the whole section, where it is not — and *"Neither use is removable by progress on the
other"* is a two-element universal over a three-element set.  The three are tabulated in
`## What is *not* here` below.  ⚠️ **The bound needs only the collapse, and the uncollapsed identity
supplies it without a closure; the description needs all three, and this file pays two.**

**2. ⚠️ BUT THE FILE DOES NOT CLAIM THAT ROW IS CLOSURE-FREE, AND `#2217` IMPLIES IT MIGHT.**
`#2217`'s context note *"Background and technical notes"* puts it as a binder list that looks
general over a theorem that is not — and asks, in the description round 1 was written against,
whether the **docstring** claims the same.  ⚠️ It does not.  Quoting that theorem's docstring at
its own wrap, and eliding only the display that follows:

> **The fibre description in the shape a rung-4 consumer wants**, at every `n` with
> `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` over `F̄`: for any `P` with `n • P = S`, […]

— the closure is named, in the reach clause, on the **second** line of the docstring, which is also
the second line of the quotation.  ⚠️ **So the trap is real in the signature and absent from the
prose**, which is the direction a reach clause is supposed to work in; `#2217`'s other observation
stands unaltered, namely that the trailing *"and needs neither `[IsAlgClosed F]` nor
`[W.IsElliptic]`"* is about `finite_torsion_of_intCast_ne_zero`, cited one line earlier, and not
about the theorem it sits under.

**3. `residueDegreeN_pos` is free, and the filing's *"check this before writing a proof"* is right
to the word.**  `residueDegreeN n h p` is *definitionally*
`residueDegreeComap (mulByNEndo_algebraMap_base n h) (mulByNEndo_isIntegralElem n h) p`, so
`residueDegreeComap_pos` — which is stated for an arbitrary `φ` in
`PullbackPrincipalityTwoRationalTorsion` — applies on the nose and nothing is transported.  That is
the third index at which this has now been true, after `n = 2` and `n = 3`.  ⚠️ The filing gives
that lemma a line number and the line number is wrong; the declaration is at `:229` of that file
and its docstring opens at `:203`.  Nothing here is keyed on it, and no coordinate for it is
published in this file.

## ⚠️ What is *not* here

* **No `[n]∗` divisor identity.**  `pullbackDivisorN_single_eq_sum_torsion_of_card` and
  `pullbackDivisorN_single_projPointOfPoint_of_card` are absent; the fibre description the fourth
  group adds is what a later round reads them off, and `#2293` owns them.
  ⚠️ **The fibre description itself is no longer absent, and the table below is re-keyed for it.**
  The closure enters that layer through THREE inputs, read off the four `_of_ne_zero` proofs of
  `EllipticCurves.FunctionField.MulByNFibre` and not off any gate list, and **all three are now
  paid**:

  | closure input | paid here |
  |---|---|
  | the **count** — `card_torsion_eq_sq` | ✅ `hcard` |
  | the **collapse** — `sum_ramificationIdxN_of_ne_zero` | ✅ the bound above |
  | the **surjectivity** — `nsmul_surjective_of_two_ne_zero` | ⚠️ ✅ `hP`, and see below |

  ⚠️⚠️ **That third row used to read *"❌ irreducible"*, and the correction is `#2292`'s whole
  finding: the input is consumed POINTWISE and the table named the wrong object.**
  `card_fibre_comapProjPointN_projPointOfPoint_of_ne_zero` reaches for the surjection in exactly
  one line — `obtain ⟨P, hP⟩ := nsmul_surjective_of_two_ne_zero h2 hn0 S` — and every later step
  uses `hP` and never the surjection again.  So what the coset half consumes is not that `[n]` is
  surjective on `E(F)` but that **the one point `S` of the divisor identity has an `n`-th part**.
  ⚠️ The paragraph this row used to carry — *"Hypothesising it is not obviously right: over a
  number field it collapses the statement, since `E(F)` is finitely generated and `[n]` surjective
  forces rank `0` and `E(F)[n] = 0` against `hcard = n²` at `n ≥ 2`"* — is **not retracted and is
  what makes the distinction load-bearing**: it is an argument against hypothesising
  `Function.Surjective (n • ·)`, and it says nothing against `hP`.  ⚠️ **`hP` demonstrably
  collapses nothing**: at `n = 2` the `ℚ` certificate in `PullbackPrincipalityTwoRationalTorsion`
  discharges `hcard` **and** `hP` on a named curve with no hypothesis left over.  The
  Mordell–Weil argument is still not in this tree and is still not cited as one.

  The count is `EllipticCurves.Torsion.StructureGeneral`'s, under that file's own
  `[IsAlgClosed F]`, and it is consumed directly by
  `card_fibre_comapProjPointN_projPointOfPoint_of_ne_zero` and by
  `fibre_comapProjPointN_eq_range_of_ne_zero`.  The collapse is
  `EllipticCurves.FunctionField.MulByNInertia`'s, reached through
  `card_fibre_comapProjPointN_le_sq_of_ne_zero` and directly by
  `ramificationIdxN_eq_one_of_comapProjPointN_eq_projPointOfPoint_of_ne_zero`; it is what
  `card_fibre_comapProjPointN_le_sq_of_isSeparable` above retires, off the *uncollapsed* identity
  against the positivity pair.  ⚠️ **And the clause that used to close this bullet was *"what is
  left is the surjectivity of `[n]` on points … nothing in this tree supplies it closure-free"*.**
  Both halves of that are still TRUE of the surjection itself — `nsmul_surjective_of_two_ne_zero`
  (`EllipticCurves.Torsion.TwoTorsionOrder`) and `nsmul_surjective_of_smooth`
  (`EllipticCurves.Torsion.NsmulSmoothSurjective`) both bind `[IsAlgClosed F]`, and they are the
  whole family: `nsmul_surjective_of_root` and `nsmul_surjective_of_hasXCoordFormula` bind it too,
  and `PointsOnIdealTorsion`'s `nsmul_surjective` is about a formal group over a local ring and is
  not this statement at all — **five** declarations tree-wide matching
  `git grep -nE '^(theorem|lemma) .*nsmul_surjective'` over `EllipticCurves/**/*.lean`, **four** of
  them on `W` and every one of the four closure-bound.  ⚠️ **What was wrong is that the layer never
  needed the surjection**, which is what the re-keyed table above records.
* ⚠️ **NOT `comapProjPointN_projPointOfPoint_of_smooth`, and round 2 of this file said it was.**
  That declaration is the *place contraction*,
  `comapProjPointN n h (projPointOfPoint W P) = projPointOfPoint W (n • P)`; its `_of_ne_zero` form
  sits **outside** `section IsAlgClosed` and is already closure-free, and it is consumed by **none**
  of the four proofs above.  ⚠️ **The clause was transplanted from a true sentence about a different
  family**: `MulByNFibre`'s `card_fibre_comapProjPointN_le_sq_of_ne_zero` docstring says *"see the
  section below for what the other seven are actually gated on, which is **not** the torsion count
  and **not** the degree"*, and its subject is the **`_of_smooth`** seven, every one of whose proofs
  does pass through the contraction.  The same file's history section then excludes the fibre
  statements from the clause by name.  ⚠️ **An index-axis gate list and a closure-axis gate list are
  two lists**, and the `3`-smooth one is retired (*"**This section used to be a gate list and is now
  a history.**"*) while the closure one is live.
* **No headline.**  Neither `exists_nsmul_divisor_eq_divisor_mulByNEndo_of_card` nor
  `exists_gS_n_of_card` is stated, so ⚠️ **`hprin` is not discharged at general `n` by this file**
  and the `[IsAlgClosed F]` forms in `PullbackPrincipalityN` remain the only ones.
* **No recovery of the merged closed statements.**  `## Recovery` below recovers the retired
  `3`-smooth *signatures* of this file's own round 1, which is a different thing.  `#907`'s
  recovery of `PullbackPrincipalityN`'s `[IsAlgClosed F]` headlines belongs with the headlines.
* **No `e = 1` in general, and none at a rational point.**  `ramificationIdxN_pos`
  (`MulByNPlacePullback`) is all that is used below, and it is strictly weaker.
* **Nothing is moved.**  `#2217` says in terms that relocating
  `pullbackDivisorN_single_eq_sum_torsion_of_ne_zero` out of `section IsAlgClosed` is not what it
  asks for and cannot be done, the closure being load-bearing there.

## Recovery

⚠️ **The `3`-smooth signatures round 1 shipped are strictly weaker than the general ones and are
recovered, not lost.**  `intCast_ne_zero_of_smooth` is the bridge — `h2`, `h3`, `n ≠ 0` and `hfac`
give `(n : F) ≠ 0` by `Nat.exists_eq_two_pow_mul_three_pow` — and three anonymous `example`s below
state round 1's six-hypothesis sandwich and its two separability forms verbatim and prove each from
the four-hypothesis general form.  ⚠️ **So `(3 : F) ≠ 0` and `hfac` are discharged rather than
used, and nothing this file used to state has been given up.**

The converse fails, and the certificate for that is `exampleFiveReach`: the sandwich at `n = 5`.
⚠️ `hfac` is false there over **every** field — `(5).primeFactors = {5}` and `5 ∉ {2, 3}` — while
`(5 : F) ≠ 0` is a hypothesis the statement binds and any field of characteristic other than `5`
discharges.  So the retired signatures cannot state that theorem at all, at any base field.

## Non-vacuity (`#916`)

⚠️ **`hcard` admits no `ℚ` certificate at any `n ≥ 3` and the reason is not a missing fixture.**
`Nat.card (W.torsion n) = n²` makes `E[n] ⊆ E(F)`, and Galois-equivariance of a surjective Weil
pairing `e_n` then forces `μ_n ⊆ F`; at `n = 3` that is `ℚ(ζ₃) ⊆ ℚ`, false, and at every larger `n`
it is worse.  `#2215`'s module docstring works the arithmetic out at `n = 3` and the same
computation governs here.

⚠️ **`n = 2` is the only index where the obstruction vanishes** — `μ₂ = {±1}` — and that index
already has its certificate, in `PullbackPrincipalityTwoRationalTorsion` on
`EllipticCurves.Fixture.y2EqX3Add5X2Add4X`, `y² = x³ + 5x² + 4x`.
**So the `_of_card` statements below are certified jointly satisfiable by the `n = 2` rung and by
nothing in this file, and that is stated rather than papered over.**

⚠️ **`hP` adds nothing to that obstruction and the `n = 2` certificate covers it too.**  The three
fibre statements bind `hcard` **and** `hP`, and the `n = 2` rung's certificate discharges both on
that curve with no hypothesis left over — so the pair is satisfiable over a field that is not
algebraically closed, and the index at which this file cannot certify it is `n ≥ 3` for the reason
above and for no reason involving `hP`.  ⚠️ **This is the whole difference between `hP` and the
surjectivity hypothesis `#2292` warns against**, which would be jointly unsatisfiable with `hcard`
at every `n ≥ 2` over a number field: `hP` asks one point for one preimage, not `E(F)` for all of
them.

What *is* committed below, over `ℚ` and at `n = 5`, is the half that carries no `hcard`: the
positivity pair and the fibre bound, on `EllipticCurves.Fixture.y2EqX3SubX`.  ⚠️ **`n = 5` is
chosen on purpose** — it is the index outside `{2, 3}` that the whole function-field front stopped
at, it is not `3`-smooth, and it is therefore a certificate that the scope correction above is a
fact about the statements and not only about their wording.  The transcendence hypothesis is
produced and not assumed, by `transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`
(`EllipticCurves.FunctionField.MulByNXCoordFormula`) from `(2 : ℚ) ≠ 0` and `((5 : ℤ) : ℚ) ≠ 0`,
and the separability the fibre bound needs comes from
`isSeparable_mulByNEndoFieldRange_of_charZero` (`EllipticCurves.FunctionField.MulByNInertia`), not
from `hcard` — over `ℚ` that is the available route and it carries no closure.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.
-/

open Module IsLocalRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]
  [DecidableEq F] [W.IsElliptic]

namespace CoordinateRing

/-! ### The Galois package at a rational `E[n]` -/

omit [IsDedekindDomain W.CoordinateRing] [W.IsElliptic] in
/-- **`|E[n]| = n²` in the multiplicative packaging**, from the count rather than from the closure.
This is `card_torsionNMul_of_ne_zero` (`EllipticCurves.FunctionField.TranslationActionN`) with
`hcard` in place of `[IsAlgClosed F]`, and ⚠️ **it drops `h2` and the index hypothesis with it**:
those are there to produce the *count*, and here the count is the hypothesis.

⚠️ The `convert` is the whole `DecidableEq` bridge of this file, exactly as at `n = 3`:
`TorsionNMul W n` bakes in `Classical.propDecidable` while `hcard` is stated at the ambient binder,
and the two are propositionally but not syntactically equal.  It is discharged by
`Subsingleton.elim`. -/
theorem card_torsionNMul_of_card {n : ℕ} (hcard : Nat.card (W.torsion n) = n ^ 2) :
    Nat.card (TorsionNMul W n) = n ^ 2 :=
  (Nat.card_congr Multiplicative.toAdd).trans (by convert hcard)

omit [IsDedekindDomain W.CoordinateRing] [W.IsElliptic] in
/-- `E[n]` is finite once it has `n²` elements, at every `n ≠ 0`.  ⚠️ `hn` is where `n` first
constrains anything in this file, and it is needed only to know `n² ≠ 0`.  The `_of_ne_zero`
sibling derives the same `n ≠ 0` from `(n : F) ≠ 0` inside its proof; here it is the hypothesis,
which is strictly weaker. -/
theorem finite_torsionNMul_of_card {n : ℕ} (hn : n ≠ 0) (hcard : Nat.card (W.torsion n) = n ^ 2) :
    Finite (TorsionNMul W n) :=
  Nat.finite_of_card_ne_zero (by rw [card_torsionNMul_of_card hcard]; exact pow_ne_zero 2 hn)

omit [IsDedekindDomain W.CoordinateRing] in
open Classical in
/-- **Artin's theorem for the translation action**, at a rational `E[n]`:
`[F(W) : Fixed(E[n])] = n²`.  `finrank_fixedFieldN_of_ne_zero` (`MulByNGalois`) with `hcard` in
place of `[IsAlgClosed F]`; the proof is unchanged, and ⚠️ **`h2` goes with the closure**, because
in the merged form it is there only to produce the count that `hcard` now supplies.  The `Fintype`
is manufactured inside the proof and never appears in a statement, as there. -/
theorem finrank_fixedFieldN_of_card {n : ℕ} (hn : n ≠ 0)
    (hcard : Nat.card (W.torsion n) = n ^ 2) :
    finrank ↥(fixedFieldN W n) W.FunctionField = n ^ 2 := by
  haveI := finite_torsionNMul_of_card hn hcard
  haveI : Fintype (TorsionNMul W n) := Fintype.ofFinite _
  have h : finrank ↥(FixedPoints.subfield (TorsionNMul W n) W.FunctionField) W.FunctionField
      = n ^ 2 := by
    rw [FixedPoints.finrank_eq_card (TorsionNMul W n) W.FunctionField, ← Nat.card_eq_fintype_card,
      card_torsionNMul_of_card hcard]
  exact h

omit [IsDedekindDomain W.CoordinateRing] in
open Classical in
/-- **`Fixed(E[n]) = [n]∗F(W)` at a rational `E[n]`**, at every `n` with `(2 : F) ≠ 0` and
`(n : F) ≠ 0`.  The sandwich of `fixedFieldN_eq_mulByNFieldRange_of_ne_zero`: both outer degrees
are `n²`, the inner inclusion is `mulByNEndo_mem_fixedPoints`, and
`IntermediateField.eq_of_le_of_finrank_eq'` closes it.

⚠️ **The degree is `finrank_mulByNFieldRange_eq_sq_of_two_ne_zero`
(`EllipticCurves.FunctionField.MulByNDegreeGeneral`), which binds no `(3 : F) ≠ 0` and no
`3`-smoothness** — see `## Why every n with (n : F) ≠ 0` for what round 1 of this file got wrong
here.  ⚠️ The transcendence proof `h` is a *parameter of the statement*, because the subfield whose
degree is measured depends on it, while that lemma **fixes** its own; the two agree because
`Transcendental` is a `Prop` and proof irrelevance is definitional, and `hdeg` below typechecks
against `h` for that reason and no other. -/
theorem fixedFieldN_eq_mulByNFieldRange_of_card (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : (n : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hcard : Nat.card (W.torsion n) = n ^ 2) :
    (mulByNEndoAlgHom n h).fieldRange = fixedFieldN W n := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hdeg : finrank ↥(mulByNEndoAlgHom (W := W) n h).fieldRange W.FunctionField = n ^ 2 :=
    finrank_mulByNFieldRange_eq_sq_of_two_ne_zero h2 (by exact_mod_cast hn)
  haveI : FiniteDimensional ↥(mulByNEndoAlgHom (W := W) n h).fieldRange W.FunctionField :=
    Module.finite_of_finrank_pos (by rw [hdeg]; exact pow_pos (Nat.pos_of_ne_zero hn0) 2)
  refine IntermediateField.eq_of_le_of_finrank_eq' ?_
    (by rw [hdeg, finrank_fixedFieldN_of_card hn0 hcard])
  rintro _ ⟨f, rfl⟩
  exact mulByNEndo_mem_fixedPoints n h f

omit [IsDedekindDomain W.CoordinateRing] in
open Classical in
/-- The `Subfield`-level sandwich at a rational `E[n]`; `SetLike.ext` off the headline, exactly as
in `fixedPoints_subfield_eq_mulByNEndoFieldRange_of_ne_zero` (`MulByNGalois`). -/
theorem fixedPoints_subfield_eq_mulByNEndoFieldRange_of_card (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : (n : F) ≠ 0) (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hcard : Nat.card (W.torsion n) = n ^ 2) :
    FixedPoints.subfield (TorsionNMul W n) W.FunctionField
      = (mulByNEndo (W := W) n h).fieldRange := by
  refine SetLike.ext fun g => ?_
  have hg : g ∈ fixedFieldN W n ↔ g ∈ (mulByNEndo (W := W) n h).fieldRange := by
    rw [← fixedFieldN_eq_mulByNFieldRange_of_card h2 hn h hcard]
    exact Iff.rfl
  exact hg

omit [IsDedekindDomain W.CoordinateRing] in
open Classical in
/-- **`F(W)` is normal over `[n]∗F(W)` at a rational `E[n]`**, over an arbitrary field with
`(2 : F) ≠ 0` and `(n : F) ≠ 0` — `FixedPoints.normal` against the sandwich.

⚠️ Normality is *not* what `#2217` asked for and round 1 of this file recorded in terms that it had
not been read.  It is here because reading it was the cost of the module docstring's
`## The reading of the headline claim`, which is a claim about the whole `_of_ne_zero` family:
once that family is the sibling table, the normality rungs are members of it,
and leaving them out would have made the universal an untested restriction rather than a
measurement. -/
theorem normal_mulByNFieldRange_of_card (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : (n : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hcard : Nat.card (W.torsion n) = n ^ 2) :
    Normal ↥(mulByNEndoAlgHom (W := W) n h).fieldRange W.FunctionField := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  haveI := finite_torsionNMul_of_card hn0 hcard
  haveI : Normal ↥(fixedFieldN W n) W.FunctionField := inferInstanceAs
    (Normal ↥(FixedPoints.subfield (TorsionNMul W n) W.FunctionField) W.FunctionField)
  rw [fixedFieldN_eq_mulByNFieldRange_of_card h2 hn h hcard]
  infer_instance

omit [IsDedekindDomain W.CoordinateRing] in
open Classical in
/-- **`F(W) / [n]∗F(W)` is separable at a rational `E[n]`**, over an arbitrary field with
`(2 : F) ≠ 0` and `(n : F) ≠ 0`, in the `IntermediateField` presentation.

⚠️ **No `CharZero`.**  Separability comes from Mathlib's instance on `FixedPoints.subfield` for a
finite group, which fires once `Finite (TorsionNMul W n)` is available from `hcard`, and is then
carried across the sandwich by `rw`.  ⚠️ **This is the route
`isSeparable_mulByNFieldRange_of_ne_zero` takes and NOT the route
`isSeparable_mulByNFieldRange_of_smooth` takes** — the latter multiplies up
from `n = 2` and `n = 3`, which is where its `3`-smoothness is created, and `MulByNGalois`'s module
docstring is the account of the difference.  That is why the sibling table of this file is the
`_of_ne_zero` family and why the headline claim is replaceability and not routing.

`isSeparable_mulByNEndoFieldRange_of_charZero`
(`EllipticCurves.FunctionField.MulByNInertia`) is *not* what a `_of_card` consumer needs: it asks
`[CharZero F]`, which is a hypothesis on `F` and not a rationality fact about `E[n]`. -/
theorem isSeparable_mulByNFieldRange_of_card (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : (n : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hcard : Nat.card (W.torsion n) = n ^ 2) :
    Algebra.IsSeparable ↥(mulByNEndoAlgHom (W := W) n h).fieldRange W.FunctionField := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  haveI := finite_torsionNMul_of_card hn0 hcard
  haveI : Algebra.IsSeparable ↥(fixedFieldN W n) W.FunctionField := inferInstanceAs
    (Algebra.IsSeparable ↥(FixedPoints.subfield (TorsionNMul W n) W.FunctionField)
      W.FunctionField)
  rw [fixedFieldN_eq_mulByNFieldRange_of_card h2 hn h hcard]
  infer_instance

omit [IsDedekindDomain W.CoordinateRing] in
open Classical in
/-- **`F(W) / [n]∗F(W)` is Galois at a rational `E[n]`**, over an arbitrary field with
`(2 : F) ≠ 0` and `(n : F) ≠ 0`.  Both halves come from the same fixed field. -/
theorem isGalois_mulByNFieldRange_of_card (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : (n : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hcard : Nat.card (W.torsion n) = n ^ 2) :
    IsGalois ↥(mulByNEndoAlgHom (W := W) n h).fieldRange W.FunctionField :=
  haveI := isSeparable_mulByNFieldRange_of_card h2 hn h hcard
  haveI := normal_mulByNFieldRange_of_card h2 hn h hcard
  ⟨⟩

omit [IsDedekindDomain W.CoordinateRing] in
/-- **Normality in the `Subfield` presentation** at a rational `E[n]`, carried across
`mulByNFieldRangeEquivSubfield` (`#1219`), the identity on elements. -/
theorem normal_mulByNEndoFieldRange_of_card (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : (n : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hcard : Nat.card (W.torsion n) = n ^ 2) :
    Normal ↥(mulByNEndo (W := W) n h).fieldRange W.FunctionField := by
  haveI := normal_mulByNFieldRange_of_card h2 hn h hcard
  exact Normal.of_equiv_equiv (f := mulByNFieldRangeEquivSubfield n h)
    (g := RingEquiv.refl W.FunctionField) (by ext a; rfl)

omit [IsDedekindDomain W.CoordinateRing] in
/-- **Separability in the `Subfield` presentation**, which is the one a fibre count consumes, at a
rational `E[n]` and over an arbitrary field with `(2 : F) ≠ 0` and `(n : F) ≠ 0`.  Carried across
`mulByNFieldRangeEquivSubfield` (`#1219`).

⚠️ **This is the declaration that keeps `hsep` off the headlines a later round states**: it is what
`sum_ramificationIdxN_mul_residueDegreeN_of_isSeparable_of_ne_zero`
(`EllipticCurves.FunctionField.MulByNInertia`) and `card_fibre_comapProjPointN_le_sq_of_isSeparable`
below consume.  ⚠️ The `3`-smooth `sum_…_of_isSeparable` in the same file is **not** the form to
plan the fibre round against; the `_of_ne_zero` form is, and it runs at every `n` with
`(2 : F) ≠ 0` and `(n : F) ≠ 0` over an arbitrary field. -/
theorem isSeparable_mulByNEndoFieldRange_of_card (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : (n : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hcard : Nat.card (W.torsion n) = n ^ 2) :
    Algebra.IsSeparable ↥(mulByNEndo (W := W) n h).fieldRange W.FunctionField := by
  haveI := isSeparable_mulByNFieldRange_of_card h2 hn h hcard
  exact Algebra.IsSeparable.of_equiv_equiv (mulByNFieldRangeEquivSubfield n h)
    (RingEquiv.refl W.FunctionField) (by ext a; rfl)

omit [IsDedekindDomain W.CoordinateRing] in
/-- **`F(W) / [n]∗F(W)` is Galois, in the `Subfield` presentation**, at a rational `E[n]`. -/
theorem isGalois_mulByNEndoFieldRange_of_card (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : (n : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hcard : Nat.card (W.torsion n) = n ^ 2) :
    IsGalois ↥(mulByNEndo (W := W) n h).fieldRange W.FunctionField :=
  haveI := isSeparable_mulByNEndoFieldRange_of_card h2 hn h hcard
  haveI := normal_mulByNEndoFieldRange_of_card h2 hn h hcard
  ⟨⟩

/-! ### The two positivity rungs, at an arbitrary place and an arbitrary index -/

omit [DecidableEq F] in
/-- **`f_p > 0` for `[n]∗`, at every place of the projective curve and every `n` at which `[n]` is
non-constant** — the instantiation of `residueDegreeComap_pos`
(`EllipticCurves.FunctionField.PullbackPrincipalityTwoRationalTorsion`), which is stated for an
arbitrary `φ`.  ⚠️ It applies **on the nose**: `residueDegreeN n h` is *definitionally*
`residueDegreeComap (mulByNEndo_algebraMap_base n h) (mulByNEndo_isIntegralElem n h)`, so nothing is
transported.  `#2217` predicted this and it is the third index at which it has held.

⚠️ No `hcard`, no index hypothesis beyond `h`, no separability, no module-finiteness and no
fibre-membership hypothesis: this holds at *every* `p : ProjPoint W`, not only at the places lying
over a named `q`. -/
theorem residueDegreeN_pos (n : ℕ) (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (p : ProjPoint W) : 0 < residueDegreeN n h p :=
  residueDegreeComap_pos (mulByNEndo_algebraMap_base n h) (mulByNEndo_isIntegralElem n h) p

omit [DecidableEq F] in
/-- Every summand of the uncollapsed fundamental identity is at least `1`, which is what turns a sum
of `n²` into a bound on the number of places.  Both factors are positive: `e_p` by
`ramificationIdxN_pos` (`MulByNPlacePullback`) and `f_p` by the previous lemma.

⚠️ Like the two positivity lemmas it rests on, this is a statement about an *arbitrary* place and an
arbitrary index: it needs neither separability nor membership of a fibre.  Only the identity
`∑ e_p · f_p = n²` those summands will be compared against needs those, which is why `hsep`
survives on the fibre bound below and not here. -/
theorem one_le_ramificationIdxN_mul_residueDegreeN (n : ℕ)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (p : ProjPoint W) :
    1 ≤ (ramificationIdxN n h p).toNat * residueDegreeN n h p := by
  have he : 0 < (ramificationIdxN n h p).toNat := by
    have := ramificationIdxN_pos n h p; omega
  have hf := residueDegreeN_pos n h p
  exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))

/-! ### The fibre bound the two positivity rungs buy -/

omit [DecidableEq F] in
/-- **At most `n²` places lie above any place of `[n]∗F(W)`**, over an arbitrary field at every `n`
with `(2 : F) ≠ 0` and `(n : F) ≠ 0`, with separability carried as a hypothesis.

`card_fibre_comapProjPointN_le_sq_of_ne_zero` (`EllipticCurves.FunctionField.MulByNFibre`) is this
bound over `F̄`, where it comes from the **collapsed** `∑ e_p = n²`.  Here it comes from the
uncollapsed `∑ e_p · f_p = n²`
(`sum_ramificationIdxN_mul_residueDegreeN_of_isSeparable_of_ne_zero`,
`EllipticCurves.FunctionField.MulByNInertia`), whose summands are bounded below by `1` for the two
independent reasons above.  The general-`n` form of
`card_fibre_comapProjPointTwo_le_four_of_isSeparable`.

⚠️ `hsep` is a hypothesis and not `hcard`, exactly as at `n = 2`, because the two available sources
of it are different theorems: `isSeparable_mulByNEndoFieldRange_of_card` above at a rational `E[n]`,
and `isSeparable_mulByNEndoFieldRange_of_charZero` (`MulByNInertia`) in characteristic zero.  ⚠️ The
`ℚ` certificate below uses the **second**, since the first is vacuous over `ℚ` at `n ≥ 3`. -/
theorem card_fibre_comapProjPointN_le_sq_of_isSeparable (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : (n : F) ≠ 0) (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hsep : Algebra.IsSeparable ↥(mulByNEndo (W := W) n h).fieldRange W.FunctionField)
    (q : ProjPoint W) :
    (finite_comapProjPointN_preimage_singleton n h q).toFinset.card ≤ n ^ 2 := by
  rw [Finset.card_eq_sum_ones,
    ← sum_ramificationIdxN_mul_residueDegreeN_of_isSeparable_of_ne_zero h2 hn h hsep q]
  exact Finset.sum_le_sum fun p _ => one_le_ramificationIdxN_mul_residueDegreeN n h p

/-! ### The fibre at a rational point, from a HALVING POINT and not from surjectivity

⚠️ **This is the section `#2292` asked for, and its finding is that the third closure input of
`## What is *not* here`'s table is consumed POINTWISE.**  `MulByNFibre`'s
`card_fibre_comapProjPointN_projPointOfPoint_of_ne_zero` reaches for
`nsmul_surjective_of_two_ne_zero` exactly once, in one line —
`obtain ⟨P, hP⟩ := nsmul_surjective_of_two_ne_zero h2 hn0 S` — and every later use is of `hP` and
never of the surjection again.  So what the coset half of the fibre count consumes is not that
`[n]` is surjective on `E(F)` but that **the one point `S` of the divisor identity has an `n`-th
part**, and that is a hypothesis rather than a closure.

⚠️ **It is also not a new design: `n = 2` already ships exactly this shape.**
`card_fibre_comapProjPointTwo_projPointOfPoint_of_card`, `fibre_comapProjPointTwo_eq_range_of_card`
and `ramificationIdxTwo_eq_one_of_card` (`PullbackPrincipalityTwoRationalTorsion`) all carry
`{S P : W.Point} (hP : 2 • P = S)`, and that file's `## Recovery` feeds them
`exists_nsmul_two_eq (Point.some x y h)` — surjectivity **at that one point** — to get the
`[IsAlgClosed F]` forms back.  The three theorems below are those three at a general index.

⚠️ **And `hP` collapses nothing, which is the whole point of the distinction.**  Hypothesising
`Function.Surjective (n • · : W.Point → W.Point)` beside `hcard` is what a number-field argument
makes jointly unsatisfiable at `n ≥ 2` (`#2292`; the argument is Mordell–Weil and is not in this
tree).  `hP` is one point having one preimage: at `n = 2` the `ℚ` certificate in
`PullbackPrincipalityTwoRationalTorsion` discharges `hcard` **and** `hP` on a named curve with no
hypothesis left, so the pair is satisfiable over a field that is not algebraically closed.  ⚠️ What
this file cannot certify is the pair at `n ≥ 3`, and the reason is `hcard` alone — see
`## Non-vacuity`, which is unchanged by this section.

⚠️ **The bound above is what makes these closure-free, and it is the only new ingredient.**  Over
`F̄` the `≤ n²` half comes from the collapsed identity and the `≥ n²` half from the coset; here the
`≤` half is `card_fibre_comapProjPointN_le_sq_of_isSeparable` off the *uncollapsed* identity, and
the `≥` half is the same coset with `hcard` in place of `card_torsion_eq_sq` and `hP` in place of
the surjection.  Both halves of the closure this layer used to need are therefore paid, and the
third input never existed in the strength the table gave it. -/

/-- **The fibre of `[n]` over a rational point has exactly `n²` elements**, over an arbitrary field
at every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`, at a rational `E[n]` and a halving `P`,
with separability carried as a hypothesis exactly as on the bound above.

`≤ n²` is `card_fibre_comapProjPointN_le_sq_of_isSeparable` above; `≥ n²` is the coset
`{ P ⊕ R : R ∈ E[n] }`, which lies in the fibre by `comapProjPointN_add_torsion_of_ne_zero` and has
`n²` distinct elements by `hcard` and `projPointOfPoint_add_injective` — ⚠️ **both of those are
already closure-free on `main`, sitting above `MulByNFibre`'s `section IsAlgClosed` at `:735` and
`:378`.**

This is `card_fibre_comapProjPointN_projPointOfPoint_of_ne_zero` (`MulByNFibre`) with `hcard`
replacing `card_torsion_eq_sq`, `hsep` replacing the collapse and `hP` replacing
`nsmul_surjective_of_two_ne_zero`, and it is the general-`n` form of
`card_fibre_comapProjPointTwo_projPointOfPoint_of_card`. -/
theorem card_fibre_comapProjPointN_projPointOfPoint_of_card (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hsep : Algebra.IsSeparable ↥(mulByNEndo (W := W) n h).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion n) = n ^ 2) {S P : W.Point} (hP : n • P = S) :
    (finite_comapProjPointN_preimage_singleton n h (projPointOfPoint W S)).toFinset.card
      = n ^ 2 := by
  classical
  have hn' : (n : F) ≠ 0 := by exact_mod_cast hn
  haveI := W.finite_torsion_of_intCast_ne_zero h2 hn'
  haveI := Fintype.ofFinite (W.torsion n)
  refine le_antisymm (card_fibre_comapProjPointN_le_sq_of_isSeparable h2 hn' h hsep _) ?_
  have hc : Fintype.card (W.torsion n) = n ^ 2 := by rw [← Nat.card_eq_fintype_card, hcard]
  rw [← hc, ← Finset.card_univ]
  exact Finset.card_le_card_of_injOn (fun R => projPointOfPoint W (P + R))
    (fun R _ => (Set.Finite.mem_toFinset _).2
      (comapProjPointN_add_torsion_of_ne_zero h2 hn h hP R))
    (Set.injOn_of_injective (projPointOfPoint_add_injective n P))

/-- **The fibre of `[n]` over a rational point *is* the coset `{ P ⊕ R : R ∈ E[n] }`**, over an
arbitrary field at every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`, at a rational `E[n]`, a
halving `P` and separability: `n²` distinct elements inside an `n²`-element set, and no further
geometry.

⚠️ **This is the declaration `## What is *not* here` records as unavailable closure-free** —
`fibre_comapProjPointN_eq_range_of_ne_zero` (`MulByNFibre`) sits inside that file's
`section IsAlgClosed` — and it is available here because its three closure inputs are `hcard`,
`hsep` and `hP`. -/
theorem fibre_comapProjPointN_eq_range_of_card (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hsep : Algebra.IsSeparable ↥(mulByNEndo (W := W) n h).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion n) = n ^ 2) {S P : W.Point} (hP : n • P = S) :
    comapProjPointN n h ⁻¹' {projPointOfPoint W S}
      = Set.range fun R : W.torsion n => projPointOfPoint W (P + R) := by
  classical
  have hn' : (n : F) ≠ 0 := by exact_mod_cast hn
  haveI := W.finite_torsion_of_intCast_ne_zero h2 hn'
  haveI := Fintype.ofFinite (W.torsion n)
  have hfin := finite_comapProjPointN_preimage_singleton n h (projPointOfPoint W S)
  have hsub : (Set.range fun R : W.torsion n => projPointOfPoint W (P + R))
      ⊆ comapProjPointN n h ⁻¹' {projPointOfPoint W S} := by
    rintro p ⟨R, rfl⟩
    exact comapProjPointN_add_torsion_of_ne_zero h2 hn h hP R
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ hfin).symm
  have hfibre : (comapProjPointN n h ⁻¹' {projPointOfPoint W S}).ncard = n ^ 2 := by
    rw [Set.ncard_eq_toFinset_card _ hfin]
    exact card_fibre_comapProjPointN_projPointOfPoint_of_card h2 hn h hsep hcard hP
  have hcoset : (Set.range fun R : W.torsion n => projPointOfPoint W (P + R)).ncard = n ^ 2 := by
    rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective (projPointOfPoint_add_injective n P),
      hcard]
  omega

/-- **`[n]` is unramified over a rational point**, over an arbitrary field at every `n` with
`(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`, at a rational `E[n]`, a halving `P` and separability.

The `n²` summands of the *uncollapsed* identity are each `≥ 1` and sum to `n²`, so the summand at
`p` is `1`; being a product of two positive naturals it forces `e_p = 1`.

⚠️ Compare `ramificationIdxN_eq_one_of_comapProjPointN_eq_projPointOfPoint_of_ne_zero`
(`MulByNFibre`), which reads the same conclusion off the **collapsed** identity and is `F̄`-only for
that reason.  The general-`n` form of `ramificationIdxTwo_eq_one_of_card`. -/
theorem ramificationIdxN_eq_one_of_card (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hsep : Algebra.IsSeparable ↥(mulByNEndo (W := W) n h).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion n) = n ^ 2) {p : ProjPoint W} {S P : W.Point} (hP : n • P = S)
    (hp : comapProjPointN n h p = projPointOfPoint W S) :
    ramificationIdxN n h p = 1 := by
  classical
  have hn' : (n : F) ≠ 0 := by exact_mod_cast hn
  have hfin := finite_comapProjPointN_preimage_singleton n h (projPointOfPoint W S)
  set s := hfin.toFinset with hs
  have hmem : p ∈ s := (Set.Finite.mem_toFinset hfin).2 hp
  have hcards : s.card = n ^ 2 :=
    card_fibre_comapProjPointN_projPointOfPoint_of_card h2 hn h hsep hcard hP
  have hsum : ∑ r ∈ s, (ramificationIdxN n h r).toNat * residueDegreeN n h r = n ^ 2 :=
    sum_ramificationIdxN_mul_residueDegreeN_of_isSeparable_of_ne_zero h2 hn' h hsep _
  have hsplit : (ramificationIdxN n h p).toNat * residueDegreeN n h p
      + ∑ r ∈ s.erase p, (ramificationIdxN n h r).toNat * residueDegreeN n h r = n ^ 2 := by
    rw [Finset.add_sum_erase _
      (fun r => (ramificationIdxN n h r).toNat * residueDegreeN n h r) hmem]
    exact hsum
  have hlow : (s.erase p).card
      ≤ ∑ r ∈ s.erase p, (ramificationIdxN n h r).toNat * residueDegreeN n h r := by
    simpa using Finset.card_nsmul_le_sum (s.erase p)
      (fun r => (ramificationIdxN n h r).toNat * residueDegreeN n h r) 1
      (fun r _ => one_le_ramificationIdxN_mul_residueDegreeN n h r)
  have hec : (s.erase p).card = n ^ 2 - 1 := by rw [Finset.card_erase_of_mem hmem, hcards]
  have hcardpos : 1 ≤ n ^ 2 := by rw [← hcards]; exact Finset.card_pos.2 ⟨p, hmem⟩
  have hprod : 1 ≤ (ramificationIdxN n h p).toNat * residueDegreeN n h p :=
    one_le_ramificationIdxN_mul_residueDegreeN n h p
  set k := (ramificationIdxN n h p).toNat * residueDegreeN n h p with hk
  have hone : k = 1 := by omega
  have hE : (ramificationIdxN n h p).toNat = 1 :=
    Nat.eq_one_of_mul_eq_one_right (hk.symm.trans hone)
  have hepos := ramificationIdxN_pos n h p
  omega

/-! ### Recovery of round 1's `3`-smooth signatures, and the index they cannot reach

⚠️ **Round 1 of this file stated the three theorems above that bind a degree at `3`-smooth `n`
only.**  The three `example`s below state those signatures verbatim and prove each from the general
form, so `(3 : F) ≠ 0`, `n ≠ 0` and `hfac` are **discharged rather than used** and nothing is lost.
`exampleFiveReach` is the converse direction: an index the retired signatures cannot reach. -/

section Recovery

omit [IsDedekindDomain W.CoordinateRing] [DecidableEq F] in
/-- `3`-smoothness implies the index hypothesis the general statements bind, over a field of
characteristic `≠ 2, 3`.  ⚠️ This is one direction only: `n = 5` satisfies `(n : F) ≠ 0` over `ℚ`
and is not `3`-smooth. -/
private theorem intCast_ne_zero_of_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) : (n : F) ≠ 0 := by
  obtain ⟨a, b, rfl⟩ := Nat.exists_eq_two_pow_mul_three_pow n hn hfac
  push_cast
  exact mul_ne_zero (pow_ne_zero a h2) (pow_ne_zero b h3)

/-- Round 1's sandwich, in its six-hypothesis signature, from the four-hypothesis general form. -/
private example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hcard : Nat.card (W.torsion n) = n ^ 2) :
    (mulByNEndoAlgHom n h).fieldRange = fixedFieldN W n :=
  fixedFieldN_eq_mulByNFieldRange_of_card h2 (intCast_ne_zero_of_smooth h2 h3 hn hfac) h hcard

/-- Round 1's `IntermediateField` separability, in its six-hypothesis signature. -/
private example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hcard : Nat.card (W.torsion n) = n ^ 2) :
    Algebra.IsSeparable ↥(mulByNEndoAlgHom (W := W) n h).fieldRange W.FunctionField :=
  isSeparable_mulByNFieldRange_of_card h2 (intCast_ne_zero_of_smooth h2 h3 hn hfac) h hcard

/-- Round 1's `Subfield` separability, in its six-hypothesis signature. -/
private example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hcard : Nat.card (W.torsion n) = n ^ 2) :
    Algebra.IsSeparable ↥(mulByNEndo (W := W) n h).fieldRange W.FunctionField :=
  isSeparable_mulByNEndoFieldRange_of_card h2 (intCast_ne_zero_of_smooth h2 h3 hn hfac) h hcard

omit [IsDedekindDomain W.CoordinateRing] in
/-- **The sandwich at `n = 5`** — `hfac` is false there and `(5 : F) ≠ 0` is not, so this is the
machine-checked statement that the correction of `## Why every n with (n : F) ≠ 0` widened the
statements and not only their wording.  ⚠️ It is a *statement-reachability* certificate and not a
non-vacuity one: `hcard` is still a hypothesis, and `## Non-vacuity` says where it can and cannot
be discharged. -/
private theorem exampleFiveReach (h2 : (2 : F) ≠ 0) (h5 : (5 : F) ≠ 0)
    (h : Transcendental F ((5 : ℕ) • genericPoint (W := W)).xCoord)
    (hcard : Nat.card (W.torsion 5) = 5 ^ 2) :
    (mulByNEndoAlgHom 5 h).fieldRange = fixedFieldN W 5 :=
  fixedFieldN_eq_mulByNFieldRange_of_card h2 (by exact_mod_cast h5) h hcard

end Recovery

/-! ### Non-vacuity over `ℚ`, at `n = 5`

⚠️ **`hcard` cannot be certified over `ℚ` at any `n ≥ 3`, and the module docstring says why: it is
vacuous there.**  What is certified below is the half that carries no `hcard` — the positivity pair
and the fibre bound — at `n = 5`, over a base field that is **not** algebraically closed and at an
index that is **not** `3`-smooth.

⚠️ **Nothing below instantiates a `_of_card` statement**, and that is the honest reading of `#916`
here rather than an omission: a certificate would have to supply `Nat.card (E(ℚ)[5]) = 25`, which
forces `μ₅ ⊆ ℚ` and is false.  The `n = 2` rung is what shows the `_of_card` hypotheses are jointly
satisfiable at all. -/

section Nonvacuity

open EllipticCurves.Fixture

/-! The certificate curve `y² = x³ − x` is the shared `EllipticCurves.Fixture.y2EqX3SubX`, whose
single `[CharZero F]` instance also supplies `IsElliptic` here, and it is taken over `ℚ` on
purpose. -/

private lemma exampleQTwo : (2 : ℚ) ≠ 0 := by norm_num

private lemma exampleQFiveIntCast : (((5 : ℕ) : ℤ) : ℚ) ≠ 0 := by norm_num

private lemma exampleQFive : ((5 : ℕ) : ℚ) ≠ 0 := by norm_num

/-- The transcendence hypothesis at `n = 5` over `ℚ`, **produced and not assumed** —
`transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`
(`EllipticCurves.FunctionField.MulByNXCoordFormula`) from `(2 : ℚ) ≠ 0` and `((5 : ℤ) : ℚ) ≠ 0`,
with no algebraic closure. -/
private theorem exampleTranscendentalFive :
    Transcendental ℚ ((5 : ℕ) • genericPoint (W := y2EqX3SubX ℚ)).xCoord :=
  transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero exampleQTwo exampleQFiveIntCast

/-- **`f_p > 0` for `[5]∗` over `ℚ`, committed** — at an arbitrary place, with no separability,
module-finiteness or fibre hypothesis, and at an index that is not `3`-smooth. -/
private noncomputable example (p : ProjPoint (y2EqX3SubX ℚ)) :
    0 < residueDegreeN 5 exampleTranscendentalFive p :=
  residueDegreeN_pos 5 exampleTranscendentalFive p

/-- **`e_p · f_p ≥ 1` for `[5]∗` over `ℚ`, committed** — the summand bound, at an arbitrary
place. -/
private noncomputable example (p : ProjPoint (y2EqX3SubX ℚ)) :
    1 ≤ (ramificationIdxN 5 exampleTranscendentalFive p).toNat *
      residueDegreeN 5 exampleTranscendentalFive p :=
  one_le_ramificationIdxN_mul_residueDegreeN 5 exampleTranscendentalFive p

/-- **At most `25` places of `ℚ(W)` lie over any place of `[5]∗ℚ(W)`, committed** — the fibre
bound, over a field that is not algebraically closed and at an index that is not `3`-smooth.
⚠️ Separability is supplied by `isSeparable_mulByNEndoFieldRange_of_charZero`
(`EllipticCurves.FunctionField.MulByNInertia`) and **not** by `hcard`, which is unavailable here;
that is the whole reason the bound above takes `hsep` and not the count. -/
private noncomputable example (q : ProjPoint (y2EqX3SubX ℚ)) :
    (finite_comapProjPointN_preimage_singleton 5 exampleTranscendentalFive q).toFinset.card
      ≤ 5 ^ 2 :=
  card_fibre_comapProjPointN_le_sq_of_isSeparable exampleQTwo exampleQFive
    exampleTranscendentalFive
    (isSeparable_mulByNEndoFieldRange_of_charZero 5 exampleTranscendentalFive) q

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
