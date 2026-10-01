/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Field.Subfield.Basic

/-!
# Transport of the automorphism group along an equality of base subfields

For a field `K` and two subfields `S T : Subfield K` with `S = T`, the two automorphism groups
`K ≃ₐ[↥S] K` and `K ≃ₐ[↥T] K` are isomorphic, by the identity on underlying functions.

⚠️ **Nothing about elliptic curves enters this file.**  It is stated for an arbitrary field and an
arbitrary pair of equal subfields, and it imports nothing from this development — the
`EllipticCurves`-import closure of this module is empty.

## Why this file exists

An Artin-sandwich argument produces a fixed field as `FixedPoints.subfield G K`, and
`FixedPoints.toAlgAutMulEquiv` identifies `G` with `K ≃ₐ[↥(FixedPoints.subfield G K)] K` — the
automorphism group over *that* presentation of the base.  What a consumer holds is a theorem saying
the fixed field **is** some subfield it cares about, and the two automorphism groups are then
different types with the same elements.  This file is the one-declaration bridge, and it is the only
brick its two consumers — `EllipticCurves.FunctionField.MulByNGaloisGroup` for `[n]∗F(W)` and
`EllipticCurves.FunctionField.NegYGaloisGroup` for `F(x)` — had to build.

## Import weight, and ⚠️ the `^import` regex that silently under-reads it

Measured at `a0d5593` with a header-only walker (block comments skipped nesting-aware, so the
`import Mathlib` inside `Mathlib/Tactic/Rify.lean`'s docstring is not read as an edge), over this
project plus all nine `.lake/packages` — 9908 `.lean` **files**, each package's own nested
`.lake/` build tree excluded.  Files, not modules: mathlib's and proofwidgets' `lakefile.lean`
collide, so the walker indexes 9907 distinct names.  ⚠️ **A name that resolves to no file in those
trees is not an edge** — `Lean.*`, `Init.*` and `Std.*` live in the toolchain, not in the nine
packages, and counting them puts this file's total at 1146 rather than 968.  That is an 18% error
with nothing absurd about it, which is this section's whole subject.  ⚠️ **This paragraph read
`320f413` while one of the three rows below had gone stale under it; `#2300` re-took all three at
four mutually independent hands, which agree to the digit — and every cell below is identical at
`7f30e87` and `60e3031`, re-measured at each rather than argued from what those commits touched.**
⚠️ **The pair this replaced, `9837 / 9836`, was one low as well as stale**: a walker scoped to
`EllipticCurves/` misses the root aggregator `EllipticCurves.lean`, which is the same file the
control-row paragraph below names as the gap between that scoping and the all-tracked count.

| module | `EllipticCurves` closure | total closure | total under `^import\s` alone |
| --- | --- | --- | --- |
| `Galois.SubfieldAut` (this file) | **0** | **968** | 3 |
| `FunctionField.NegYGaloisGroup` | 22 | 2668 | 47 |
| `FunctionField.MulByNGaloisGroup` | 107 | 2838 | 159 |

⚠️ **The two closure columns count the module itself differently**, and assuming one convention for
both is how a re-run comes out one high on three cells.  The total counts it; the `EllipticCurves`
column does not — that column is the sense in which this file's own `EllipticCurves`-import closure
is empty, and in which `#1266` cut `NegYGaloisGroup` from 71 to 19.

⚠️ **The totals are falsifiable, and the check is a RELATION and not three numerals:
`lake build <module>` must report that row's total plus exactly `15`.**  At `a0d5593` it reports
**983**, **2683** and **2853** jobs against closures spanning 968 to 2838 — `+15` on all three
rows, so the constant is lake's non-module job set and is intact where the closures moved.  Three
numbers out of a hand-rolled walker are otherwise unfalsifiable; a constant offset against lake's
own module graph is not.  ⚠️ **A control nobody executes catches nothing, and that is the finding
here rather than three numerals**: the relation held on every row at `320f413`, and the third row
left `2802` **one day later** at `263f6e1` (2026-09-02), so run once on any of the **261** commits
from there to `a0d5593` it would have printed `2853` against a published `2817` (`#2300`).
⚠️ **Name the step commit, not the span**: across the **37** commits from `320f413` to `263f6e1`
the closure still read `2802` and the control still PASSED, and the span figure moves with every
landing where `263f6e1` does not.

The relocation that created this file is what the first column is for: on **one tree**, across the
single commit `008fea7`, `NegYGaloisGroup`'s project closure fell **71 → 19** — it is 22 at
`a0d5593`, the `EllipticCurves/` directory having grown from **359** files to **456** — while
`MulByNGaloisGroup` rose 70 → 71, the one new module being this one.  ⚠️ That saving is **52**
modules as measured here; `#1259` and `#1267` record it as 53, and the difference is the
self-counting convention: consistent counting gives 52 either way (`71 → 19` excluding the module,
`72 → 20` including it), while `72 − 19` — one convention on each side — gives 53.  ⚠️ **And the
growth figure this paragraph carried was itself one convention on each side** — the trap the
control-row paragraph below diagnoses, walked into here: *"from 359 modules to 387"* took **359**
from the `EllipticCurves/`-directory count at `008fea7` and **387** from the all-tracked count at
`320f413`, where that directory holds **386**.  They are cells of different sequences —
`359 → 386 → 439 → 456` under one and `360 → 387 → 440 → 457` under the other — and the pair above
names its scoping for that reason.

⚠️ **The third column is not a typo, and it is the reason to write this section down.**  Mathlib at
this pin uses the Lean module system, so `Mathlib/Algebra/Algebra/Equiv.lean` — this file's own
first import — opens `module` / `public import Mathlib.Algebra.Algebra.Hom`, and a script matching
`^import\s+(\S+)` reads it as importing **nothing**.  The pattern that works is

```python
re.compile(r'^(?:public |private |meta |protected )*import\s+(?:all\s+)?(\S+)')
```

⚠️ **That pattern is necessary and not sufficient: where the header ends is a second, independent
decision, and it moves the number.**  The third column is what a walker gets by reading the whole
header and ignoring lines its pattern cannot parse — the experiment that changes only the capture
pattern.  A walker that instead *stops* at the first unparsable line halts on the opening
`public import` and reports `3 / 44 / 153`; the edges it drops are ordinary non-`public` imports
placed after the public block, as `Mathlib/RingTheory/Algebraic/Integral.lean` places
`import Mathlib.RingTheory.Polynomial.Subring`.  ⚠️ **That drop is the difference of the two columns
and not a numeral**: it reads `0 / 3 / 3` at `320f413` and `0 / 3 / 6` at `a0d5593`, so the shape of
the disagreement survives a re-keying and its size does not.  ⚠️ **The first row's drop is `0` and
never was `3`** — both of its variants read `3`, so the uniformity was only ever a claim about the
second row and the third.

⚠️ **Why the bug does not announce itself.**  Nothing in this development writes `public import`, so
the *project* column is exact under either pattern and every project-side sanity check passes.  Only
the total is wrong, and it is wrong by a factor of 18 (`2838 / 159`) to 323 (`968 / 3`) — a number
small enough to look like a plausible import count rather than an absurd one.  Census, `.lean` files
/ with a `^public import ` line / with a plain `^import ` line.  ⚠️ **The rows are not scoped
alike**: mathlib's is `Mathlib/` only, every other package's is the whole package tree minus its
nested `.lake/`.  Scoping the others the way mathlib's is scoped — to `batteries/Batteries`,
`aesop/Aesop`, … — reads batteries as 187 files rather than 254, and shifts every row but mathlib's
and the project's.

| tree | files | `^public import ` | `^import ` |
| --- | --- | --- | --- |
| `EllipticCurves/` | 439 | **0** | **439** |
| `.lake/packages/mathlib/Mathlib` | 8264 | **8246** | 381 |
| `.lake/packages/batteries` | 254 | 127 | 82 |
| `.lake/packages/aesop` | 250 | 125 | 161 |
| `.lake/packages/proofwidgets` | 46 | 25 | 5 |
| `.lake/packages/importGraph` | 37 | 18 | 22 |
| `.lake/packages/Qq` | 28 | 12 | 15 |
| `.lake/packages/plausible` | 28 | 6 | 17 |
| `.lake/packages/Cli` | 5 | 3 | 2 |
| `.lake/packages/LeanSearchClient` | 8 | 0 | 0 |

⚠️ **The project row is the control, and the control is a RELATION and not three numerals**:
column 2 must be `0` and column 3 must EQUAL column 1 — no `public import `, a plain `^import `
in *every* file.  Both hold at `9f25690`: `439 / 0 / 439`.  ⚠️ **Why only this row rots: below.**

⚠️ **The module system is a toolchain convention, not a Mathlib one.**  **Eight** of the nine
vendored packages use `public import` — every one but `LeanSearchClient`, and ⚠️ **the reason is
not that it has no `import` lines**: it writes all **18** of them, across all **8** of its files,
as `public meta import`, matching neither column of the census table above.  Scoping a verification
`grep` to `Mathlib/` bounds the blind spot over Mathlib alone, while every closure above walks all
nine.  The same holds for `import all M`, which suppresses nothing but must still be matched:
`Mathlib/` writes it 23 times in 21 files, `MathlibTest/` in 10 more, and **Batteries in 13** — of
the **10** `import all` modules inside this file's own closure, **5 are Batteries'**.

⚠️ **TWO modifiers is the second blind spot, and it is this section's own lesson turned on this
section.**  The pattern printed above carries it — that group is starred, not optional — and the
census table does not, which is how an exact `LeanSearchClient` row and a false sentence drawn
from it came to sit beside each other.  Files carrying at least one matching line, at `6f051d4`,
over each package tree minus its nested `.lake/` (**9451** `.lean` files) — ⚠️ **which is the
census table's scoping for eight of that table's ten rows and NOT for mathlib's, whose row is
`Mathlib/` only, so the two do not sum together.**  Read under the census table's own scoping
these three rows are **8562** / **8563** / **8647** over **8920** files, a gap of **84**:

| pattern | files |
| --- | --- |
| `^public import ` — the census table's own column | **8578** |
| exactly ONE of `public`, `private`, `meta`, then `import ` | **8580** |
| ⚠️ ONE OR MORE of them, then `import ` — that pattern's group, made non-empty | ⚠️ **8665** |

⚠️ **The gap is `public meta` and nothing else**: it is the only prefix occurring in any of the
**85** files the last row adds, and those fall in **8** of the nine packages, `Cli` alone
excepted.  ⚠️ **The scoping moves the size and not the shape** — walking `.lake/packages` whole,
nested build trees included, reads **10107** / **8894** / **8897** / **9057** for a gap of
**160**, and the entire difference is mathlib's own vendored copies: the same eight packages, the
same single prefix, and `LeanSearchClient`'s **8** either way, since it vendors nothing.

⚠️ **The third row is that pattern's GROUP and not the pattern.**  The group printed above is
starred, so run verbatim over these same **9451** files the pattern matches **9401** — every file
carrying an `import` line of any shape, the **50** it misses having none at all — and **8665** is
what the group returns only once it is required to repeat.  ⚠️ **`protected`, which that pattern
names and these rows do not, is inert**: a prefix census over all **10564** `.lean` files of both
trees at `e1c56c14` — **10107** vendored and **457** project, ⚠️ **both terms a whole-tree `find`
with nothing excluded on either side** — reads `{public: 35205, public meta: 965, meta: 13}`, with
`private import` never occurring either, so the three-modifier alternation above returns the same
**8665** as the four.

⚠️ **That population is a SUM with one pinned term, and saying so is what makes the cell cheap**:
`<both trees> = 10107 + <project .lean files>`, the vendored term pin-bound and the project term
the only live measurement in it, so a reader re-derives the cell from one `find` and localises any
future drift to the project half in one reading.  ⚠️ **The cell read `10546` until `#2303`**: that
was `10107 + 439`, and the `439` was the census control row's value at `9f25690` — ⚠️ **a sha this
sentence never named, inherited from a row fifty lines above it**.  ⚠️ **Its two terms were not
scoped alike either**: `439` is the `EllipticCurves/`-**directory** count set against a whole-tree
vendored `find`, so it fell short by the root aggregator `EllipticCurves.lean` as well as by the
tree's growth, and **457**, the all-tracked count, is the term that matches.  ⚠️ **The three
buckets did not move with it, and that is a relation and not luck**: no project file carries a
modifier-prefixed `import` at all — all **1758** project `import` lines are bare — so the project
term moves the population and can never move the buckets.

⚠️ **THE CENSUS TABLE'S ONLY ROT-CAPABLE ROW IS ITS CONTROL ROW — measured, not supposed, and it is
why the project row carries a ref where the nine below it need none.  ⚠️⚠️ IT SAYS NOTHING ABOUT THE
CLOSURE TABLE AT THE HEAD OF THIS SECTION, WHERE EVERY ROW CAN ROT, BECAUSE A CLOSURE OVER A GROWING
TREE GROWS.  ⚠️⚠️ AND IT SAYS NOTHING ABOUT ANYTHING THAT IS NOT A ROW — THE DISCRIMINATOR IS THE
TERM AND NOT THE TABLE.**  A figure rots exactly when some term of it reads a tree that moves.  The
nine vendored rows, `9451`, `8578` / `8580` / `8665`, the `8920`-scoped trio, `10107`, `85`, the
prefix-census buckets and the comment-mask prices read `.lake/packages` alone and are pinned for the
reason given below; every figure carrying a project term can rot, **in a table cell or in a sentence
indifferently**, and the one that did so unnoticed was `10546` — a numeral in a paragraph, which is
exactly where a row-shaped clearance does not look (`#2303`).  The earlier wording opened *"the
table's"* without naming which table, and that is how the closure table's third row stood stale from
`263f6e1` across the **261** commits to `a0d5593` under a sentence a reader takes for a clearance
(`#2300`).  ⚠️ **The observed asymmetry is worth keeping and is not a property of the table**: over
`320f413..a0d5593` a leaf with an empty project closure was inert (`968` unmoved), a 22-module
consumer happened not to move (`2668` unmoved), and the 74-module one moved to **107 / 2838**.
**Inertness is luck about where a module sits.**  The vendored rows are pinned: `lake-manifest.json`
has not moved since `74fca19` (2026-07-26), so none of them can shift without a pin bump.  The
project row tracks a live tree that **186** commits touched in `e3c0db2..9f25690`, and it drifted
`386 → 439` — `+53` in columns 1 and 3, column 2 unmoved at `0`.  ⚠️ **The row was never WRONG; it
went STALE**: at `e3c0db2`, the commit that wrote it, the relation reads `386 / 0 / 386` exactly.
**A census whose control is the first cell of it to go stale reads as broken when it is only out of
date**, which is how it read — `#2259` found it while `#2257` shipped on *"every row is exact"*,
true of the other nine.

⚠️ **Published sweep, because a rot clause whose population is withheld clears nothing.**  Over
this whole section, counting every numeral outside a sha, an issue tag, a toolchain version and a
date: **111** distinct values in **237** occurrences at the base `e1c56c14`, and **116** in **265**
here.  ⚠️ **That second pair counts itself** — a published census of the paragraph it sits in is a
fixed point — **so it was iterated to one and not estimated.**  Exactly **one** value of the base
population was a live-tree numeral carrying no ref: `10546`, paid above.  ⚠️ **Two more are
live-tree and keyed, so stale rather than wrong** — the control row `439 / 0 / 439` at `9f25690`,
which reads `456 / 0 / 456` (`#2302`), and the **3768** build-job count at the end of this section,
which reads **3769** here, `+1` for the single module `8e55647` added (`#2304`).  **Neither is
folded in and both are filed.**  ⚠️ **Publishing the population is the whole point**: it lets a
later reader disagree with the classification and not merely with the hits, which a bare
*"swept, clean"* cannot.

⚠️ **Two unit traps in that control, and the wording replaced above walked into both.**  First,
**column 3 counts FILES carrying such a line, not lines**, and the readings differ by nearly a
factor of three: at `9f25690` those 439 files carry 1260 `^import ` lines, min 1, max 10, mean
2.87 — so *"one plain `import` line per file"* is true of the file count and false of the line
count.  ⚠️ **The line figure is itself the worked example: 1257 at `6f051d4` and 1260 at
`9f25690`, two commits five minutes apart, while `439 / 0 / 439` did not move.**  Second, the
replaced sentence compared **two SCOPINGS**: its *"360 when this was first measured"* is the
all-tracked-`.lean` count and its *"386 now"* the `EllipticCurves/`-directory count — at
`008fea7`, the first commit carrying this file, the directory holds **359** and the tracked total
**360**, differing by exactly the root aggregator `EllipticCurves.lean`.  The sequence is
`359 → 386 → 439` under this row's scoping and `360 → 387 → 440` under the other.  **Do not
re-take this row without saying which, and without keying it to a commit.**

⚠️ **AND IT HAS DRIFTED AGAIN — SAID HERE AND DELIBERATELY NOT FOLDED IN.**  At `a0d5593` the
*relation* still holds: `EllipticCurves/` holds **456** files, **0** with a `^public import ` line
and **456** with a plain `^import ` one, and those files carry **1302** `^import ` lines (min 1,
max 10, mean 2.86) against `9f25690`'s 1260.  ⚠️ **So `439 / 0 / 439` is a cell keyed to a sha that
has gone stale while what it asserts is intact, and re-taking it is its own row rather than this
one's** — `#2257` / `#2259` are its history, it has been re-taken twice, and `#2300` measured it and
left it alone on purpose.  **Folding a third re-key of it into a neighbouring repair is how one
paragraph ends up carrying two keyings.**

⚠️ **Do not take a matching total as evidence your pattern is right.**  At `a0d5593`, dropping the
`(?:all\s+)?` alternative changes **none** of the three totals, because every `import all` target is
reachable by another path — so that alternative is a correctness requirement whose omission is
invisible in exactly the way `public import`'s is not.

⚠️ **The census table's two `import` columns do not partition its rows, and the number of files a
`^import` walker sees nothing whatever in is neither of them.**  Of mathlib's **381** files with a
plain `^import ` line, **372** carry a `^public import ` line as well — in those the bad pattern
under-reads rather than misses — so the files it reads as importing *nothing at all* number
**7883**, which is `8264 − 381`.  The two remainders are small and worth naming so that a re-run
recognises them: **9** files are plain-only and **9** carry neither spelling.  ⚠️ **`8246` is the
`public import ` column and is not that figure**, and naming it as the blind spot is `#1292`'s own
claim from its first round to the one that landed — `e3c0db2`'s subject line says so in terms, and
that commit is an ancestor of `main`, so it stays retrievable where that row's earlier rounds do
not.  ⚠️ **PR #471 before it stated the blind spot as a CLOSURE FACTOR and not a file count** — *"a
total of `111` for `NegYGaloisGroup` instead of `3027`"*, which it prices as a factor of thirty —
and it names this column nowhere.  These four counts are pinned with the nine vendored rows above
and cannot move without a pin bump.

⚠️ **Where the header ends has a worst case, and it is Mathlib's own root file.**
`Mathlib/Init.lean` — reached, directly or not, by very nearly every file in the library — carries
**32** imports, and the **first** of them is line 3, which reads
`public import Lean.Linter.Sets -- for the definition of linter sets`.  A capture pattern anchored
at end of line cannot parse that, so the stop-at-the-first-unparsable variant halts *before*
Mathlib's very first import and reads the root file as importing **0 of 32**; the skip variant
collects **28 of 32**, the four it drops being exactly the trailing-`--` lines 3–6.  ⚠️ **The
pattern printed above is immune because it is not anchored** — this trap lives in the anchoring
and not in the prefix group — and both variants *under*-count, which is the direction that looks
right.

⚠️ **The comment mask has a price, it is 633 modules, and ⚠️ it does not come from the file this
section's own parenthesis names.**  Dropping the nesting-aware block-comment mask and scanning whole
files, everything else held fixed, reads this module's total as **1601** rather than **968** — both
re-measured at `3f9e323`, where this row's own `0 / 968` still holds exactly.  ⚠️ **All 633 are
three files inside the closure**, each carrying a column-0 `import` line inside a docstring:
`Mathlib/Tactic/FunProp.lean`:48, worth **+584** on its own; `Mathlib/Tactic/ExtractGoal.lean`:90,
**+246**; and `Mathlib/Tactic/MinImports.lean`:31–34, **+1**.  ⚠️ **They do not sum to 633** — the
first two pull overlapping subtrees, so a per-file audit of this trap over-prices its parts.
⚠️⚠️ **`Mathlib/Tactic/Rify.lean`:68 — the `import Mathlib` named at the top of this section —
contributes ZERO here**: `Mathlib.Tactic.Rify` is in this module's closure under neither reading, so
splicing its unmasked edges into the masked graph leaves the total at **968** exactly.  **The
exemplar is sound and the price is sound; they are not the same claim**, and a walker audited only
against the named file would pass while carrying all three of the files that actually move the
number.  `MinImports`:253–256 is the live witness for the resolve-to-a-file rule stated at the top
of this section: `import A`, `import B` and `import Z` are read by the pattern and are edges under
neither reading.  These figures are pinned with the nine vendored rows above.

⚠️ **A second check on the two-consumer claim costs nothing and needs no script.**  A
docstring-only edit to this file rebuilds exactly **four** jobs — this module, its two consumers,
and the `mk_all` root `EllipticCurves` — out of the **3768** a full build reports at `3f9e323`.
*Which* modules `lake` recompiles is the fan-out claim restated from the build side, so every build
of a change to this file re-verifies it for free; it was measured on the edit that added this
paragraph.

## Mathlib has no name for this

⚠️ Re-grepped at Lean `v4.32.0` / Mathlib `v4.32.0` before this file was cut, and the position is
unchanged from when the declaration was first written:

* `AlgEquiv.autCongr` (`Mathlib/Algebra/Algebra/Equiv.lean`) moves the **top** algebra over a fixed
  base — `(A₁ ≃ₐ[R] A₂) → ((A₁ ≃ₐ[R] A₁) ≃* (A₂ ≃ₐ[R] A₂))` — and is not this;
* `IntermediateField.equivOfEq` (`Mathlib/FieldTheory/IntermediateField/Basic.lean`) is an
  `AlgEquiv` between the two intermediate fields **themselves**, not between their automorphism
  groups;
* `autCongr` is *declared* in exactly one place in Mathlib — the file above.  The three other
  Mathlib files that mention it (`FieldTheory/AbelRuffini.lean`, `FieldTheory/KummerExtension.lean`,
  `NumberTheory/Cyclotomic/Gal.lean`) are consumers of that one, not a second, base-changing
  version.

So `Subfield.autMulEquivOfEq` is an upstream candidate.  ⚠️ It is a candidate and not a plan: no
Mathlib pull request exists, and nothing in this development is waiting on one.

## ⚠️ The imports are minimal, and `Subfield.Basic` cannot be weakened to `Subfield.Defs`

Both imports were tested by deletion and both are needed.  `Mathlib.Algebra.Field.Subfield.Defs`
does make this file *elaborate* — but it makes it elaborate against a **different** `Algebra ↥S K`
instance.  Measured with `set_option pp.explicit true in #synth Algebra (↥S) K` under each import
set:

* with `Mathlib.Algebra.Field.Subfield.Basic` — `Subfield.toAlgebra`;
* with `Mathlib.Algebra.Field.Subfield.Defs` — `Algebra.ofSubsemiring …`, found through
  `SubsemiringClass`.

`Subfield.toAlgebra` (`Mathlib/Algebra/Field/Subfield/Basic.lean`) is the instance every consumer of
this file resolves, so weakening the import would put a different instance into the *statement* of
`autMulEquivOfEq` and leave consumers to unfold the difference.  ⚠️ **The narrower import is not the
better one here**; do not "optimise" it without re-running that `#synth`.

## Main definitions

Every public declaration of this file is listed, here and under `## Main statements`.  Everything is
in namespace `Subfield`.

* `Subfield.autMulEquivOfEq` — transport of `Aut K` along an equality of base subfields.

## Main statements

* `Subfield.autMulEquivOfEq_apply` and `Subfield.autMulEquivOfEq_symm_apply` — the transport is the
  identity on underlying functions, by `rfl` in both directions.

## What is *not* here

* **No `IntermediateField` twin.**  A consumer whose equality is an `IntermediateField` equality
  drops it to the `Subfield` level first — `SetLike.ext` off the equality it already has — and then
  applies these names.  `EllipticCurves.FunctionField.NegYGaloisGroup` is the worked example, in
  `fixedPoints_subfield_eq_ratFuncRange`; the `≃ₐ` types over the two carriers are definitionally
  equal, which that file commits as an `example`, so a second name here would be noise.
* **Nothing about fixed points.**  `FixedPoints.toAlgAutMulEquiv` is Mathlib's and is what this
  transports *against*; it is not restated, and this file does not import it.
* **No `Normal`, no `IsGalois`, no degree.**  An equality of base subfields carries all three across
  on its own, and no consumer needs a lemma here to say so.
-/

namespace Subfield

variable {K : Type*} [Field K] {S T : Subfield K}

/-- **Equal base subfields give isomorphic automorphism groups**, by the identity on underlying
functions.

An `S`-algebra automorphism of `K` is a ring automorphism that fixes `S` pointwise, and `S = T` says
the two subsets are the same, so nothing is transported except the proof obligation.  The
`MulEquiv` is therefore built out of `AlgEquiv.ofRingEquiv` in both directions and all three
coherence fields are `rfl`. -/
def autMulEquivOfEq (hST : S = T) : (K ≃ₐ[↥S] K) ≃* (K ≃ₐ[↥T] K) where
  toFun e := AlgEquiv.ofRingEquiv (f := (e : K ≃+* K)) fun r => e.commutes ⟨r, hST.ge r.2⟩
  invFun e := AlgEquiv.ofRingEquiv (f := (e : K ≃+* K)) fun r => e.commutes ⟨r, hST.le r.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] lemma autMulEquivOfEq_apply (hST : S = T) (e : K ≃ₐ[↥S] K) (x : K) :
    autMulEquivOfEq hST e x = e x := rfl

@[simp] lemma autMulEquivOfEq_symm_apply (hST : S = T) (e : K ≃ₐ[↥T] K) (x : K) :
    (autMulEquivOfEq hST).symm e x = e x := rfl

end Subfield
