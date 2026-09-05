/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.MulByNDegreeGeneral
import EllipticCurves.FunctionField.MulByNGalois
import EllipticCurves.FunctionField.MulByNPlaceComposition
import EllipticCurves.FunctionField.MulByNResidueDegree
import EllipticCurves.FunctionField.MulByNSeparable
import EllipticCurves.FunctionField.PlaceInertiaGeneral

/-!
# The fundamental identity for `[n]∗`: `∑_{p ↦ q} e_p · f_p = [F(W) : [n]∗F(W)]`

`EllipticCurves.FunctionField.PlaceInertiaGeneral` proves the fundamental identity at an
**arbitrary** ring endomorphism `φ` of `F(W)`, over an arbitrary base field:

```
∑_{p ↦ q} e_p · f_p = finrank (placeBelow φ q) (integralClosure (placeBelow φ q) F(W))
```

under `hφF` (`φ` fixes `F`), `hφint` (`φ` is integral), `[Module.Finite ↥φ.fieldRange F(W)]` and
`[Algebra.IsSeparable ↥φ.fieldRange F(W)]`.  Until now it was instantiated at `φ = [2]∗` only.
This file instantiates it at `φ = [n]∗`, and supplies the two instance hypotheses:

* `Module.Finite` is `module_finite_mulByNEndoFieldRange`
  (`EllipticCurves.FunctionField.MulByNIntegral`) at **every** `n` at which `[n]` is non-constant;
* `Algebra.IsSeparable` is `isSeparable_mulByNEndoFieldRange_of_smooth`
  (`EllipticCurves.FunctionField.MulByNSeparable`, `#1219`) at every `3`-smooth `n` over `F̄`, and
  — `isSeparable_mulByNEndoFieldRange_of_charZero` below — at **every** `n` in characteristic zero.

## ⚠️ The identity and the value `n²` are two different theorems, and they have different ranges

The identity's own right-hand side is a `finrank` of an integral closure, not `n²`; turning it into
`n²` is a separate step, and the two do not reach the same indices.

* **The identity** holds at every `n` at which `[n]` is non-constant and `F(W) / [n]∗F(W)` is
  separable — in particular, by the characteristic-zero route, at **every** `n` over `ℚ` or any
  other field of characteristic zero, with no `3`-smoothness and no algebraic closure.  That is
  `sum_ramificationIdxN_mul_residueDegreeN_finrank_of_charZero`.
* **The value `n²`** needs `[F(W) : [n]∗F(W)] = n²`, which
  `EllipticCurves.FunctionField.MulByNComposition` (`#1213`) proves at `3`-smooth `n` and nowhere
  else, so `sum_… = n ^ 2` carries `3`-smoothness even in characteristic zero.

⚠️ Read the `finrank` forms as the theorems and the `n ^ 2` forms as their corollaries at the
indices where the degree is known, not the other way round.  The general-`n` characteristic-zero
identity is strictly the wider statement and is lost if only the `n ^ 2` shape is remembered.

## The chain, and where each link comes from

```
sum_toNat_ramificationIdx_mul_residueDegreeComap_fibre    (PlaceInertiaGeneral, arbitrary φ)
  ⟹ ∑ e_p · f_p = finrank (placeBelowN) (integralClosure …)
finrank_integralClosure_placeBelow                        (#754, arbitrary φ)
  ⟹                = finrank ([n]∗F(W)) F(W)
finrank_mulByNFieldRange_of_smooth                        (#1213, 3-smooth n)
  ⟹                = n²
```

⚠️ There is a presentation mismatch in the middle link and it is the one mechanical obstacle in the
file.  `#1213`'s degree is stated for `mulByNEndoAlgHom` — the `IntermediateField` `fieldRange` —
while the place machinery runs on `mulByNEndo`, the `RingHom` one, because `ValuationSubring ↥L`
needs `L` to be a `Field` type and only the `Subfield` coercion is one.  `#1219`'s
`mulByNFieldRangeEquivSubfield` is the identity map between them;
`finrank_mulByNEndoFieldRange_of_smooth` below is the crossing, and it is the exact general-`n`
analogue of the merged `finrank_mulByTwoEndoFieldRange` and `finrank_mulByThreeEndoFieldRange`.

## What was already there at `n = 2` and `n = 3`, and what is genuinely new

⚠️ `#1221` was filed saying *"there is no `n = 3` instantiation at all"*.  **That is wrong**, and
the record should say so: `sum_ramificationIdxThree_mul_residueDegreeThree`
(`EllipticCurves.FunctionField.MulByThreeResidueDegree`) has been merged for months.  What is true
is narrower and still worth having:

* that theorem carries `[IsAlgClosed F]` and is proved by *collapsing* — it rewrites every `f_p` to
  `1` and quotes `sum_ramificationIdxThree_eq_nine` — so it says nothing over a base field that is
  not algebraically closed.  The `_of_isSeparable` and `_of_charZero` forms below **are** new at
  `n = 3`, and over `ℚ` the identity at `n = 3` was not available in any form;
* it is stated in the `[3]`-indexing, not the `[n]`-indexing, so no consumer holding an
  `n` can use it.  `residueDegreeN_three` (`EllipticCurves.FunctionField.MulByNResidueDegree`) and
  `sum_ramificationIdxN_mul_residueDegreeN_three` below are the bridge, and
  `sum_ramificationIdxThree_mul_residueDegreeThree_of_charZero` is the
  `[3]`-indexed statement they buy — which is, verbatim, what `MulByThreeResidueDegree`'s `## Scope`
  section **used to say** is still absent.  ⚠️ **It no longer does, and the section is `## Scope`
  and never was a `## What is not here`.**  That bullet was retired in the same commit that created
  this file (`4a30e82`, `#1221`) and now names
  `sum_ramificationIdxThree_mul_residueDegreeThree_of_charZero` — i.e. this file — as exactly what
  supplies it.  The citation is kept because it is the *reason* the statement below is written in
  the `[3]`-indexing at all; it is not a live gap.

At `n = 2`, `sum_ramificationIdxTwo_mul_residueDegreeTwo_of_isSeparable` and `…_of_charZero`
(`PlaceInertiaGeneral`) already say everything below at that index; the content there is the bridge
`sum_ramificationIdxN_mul_residueDegreeN_two`, nothing more.

## ⚠️ The transcendence parameter, and which clauses below name it

Every general-`n` declaration below whose statement mentions the `[n]∗` layer — `mulByNEndo n h`,
`comapProjPointN n h`, or anything built on them — takes
`h : Transcendental F (n • genericPoint).xCoord` as an explicit argument.  ⚠️ **That sentence is
not a reach register for `## Main results`, and this section used to say it was** (`#1668`).  It
read *"**That sentence is the register**, in the sense of `README.md` `### Module-block bullets`:
it is what tells a reader which declarations below bind `h`"* (`5dfd94d`, `#1658`, PR #664), closing
*"and no bullet of `## Main results` repeats it"* — ⚠️ **and that closing clause is a second
commit's**, so it is attributed to its own rather than folded into the first: `5dfd94d` closed
*"and no clause below repeats it"*, and PR #671 substituted the bullet form (`1354e2d`, `#1669`).
The earlier wording is retired on its own ground in the paragraph below; what is retired here is
the register claim, and with it the bullet form of its closing clause.  `README.md`
`### Module-block bullets` now fixes the unit in terms — a reach register binds *"the list it
heads"*, and this sentence heads a different `##` section — so the claim was false rather than
partial and `### Retired claims` binds.  What
this sentence is instead is the **derivability exemption's citation**, which may sit anywhere in
the module block, over a statement of fact about which declarations bind `h`; the two bullets that
hung on it are repaired in the list itself.  ⚠️ **Twelve clauses below do name it — three of them
declaration headlines, and two of them bullets of `## Main results` since that repair** —
`isSeparable_mulByNEndoFieldRange_of_charZero`'s *"at every `n` at which `[n]` is non-constant"*,
`sum_ramificationIdxN_mul_residueDegreeN_finrank`'s, which is the same clause, and
`…_finrank_of_charZero`'s, which is that clause again since `#1664` (below); the remaining
nine are listed with their recogniser below.  **What that sentence is for is the rest** — the
declarations whose clause says nothing about the non-constancy, and those that carry no index
clause at all.  Where a row's clause names `(2 : F) ≠ 0` together with an index cast, or
`(2 : F) ≠ 0`, `(3 : F) ≠ 0`, `n ≠ 0` and `3`-smoothness, the `README.md` exemption
(`## Docstring conventions` → `### Reach clauses`) is what clears it — a hypothesis derivable from
the ones the clause *does* name adds no reach — and this is the citation that exemption asks
for:

* `transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`
  (`EllipticCurves.FunctionField.MulByNXCoordFormula`) proves `h` from `(2 : F) ≠ 0` and
  `((n : ℤ) : F) ≠ 0` — the `_of_ne_zero` clauses' own hypotheses, the two cast forms being
  interderivable by `Int.cast_natCast`;
* `transcendental_xCoord_nsmul_of_smooth` (`EllipticCurves.FunctionField.MulByNComposition`) proves
  it from `(2 : F) ≠ 0`, `(3 : F) ≠ 0`, `n ≠ 0` and `3`-smoothness — the `_of_smooth` clauses' own.

⚠️ **`(2 : F) ≠ 0` fails that same test, and so stays bound.**  Nothing any reach clause in this
file names derives it — not `3`-smoothness, not `(n : F) ≠ 0` — so omitting it is not an instance of
the exemption but the defect class `#1137` is named after.

⚠️ **The general-`n` half of that sentence is a restriction, not filler.**  Several fixed-index
statements below are about that same layer and take no `h` at all: they **discharge** it inline
from their own hypotheses — the `n = 5` ones by the first lemma cited above — so the derivation is
exhibited in this file rather than only asserted about it.

⚠️ **The exemption is keyed on the clause and not on the name, and this section used to claim it
for the whole list.**  Until `#1658` the register sentence above ran straight into *"That is the
`README.md` exemption … and this is the citation it asks for"* (`01f955b`, `#1137`), which reads
as clearing every row below on that ground.  It does not reach all of them.  **Two bullets, three
declarations, carry an index clause that names neither set of hypotheses:**
`isSeparable_mulByNEndoFieldRange_of_charZero`, bulleted *"at every `n` in characteristic zero"*,
and `sum_ramificationIdxN_mul_residueDegreeN_finrank` / `…_finrank_of_charZero`, *"at every `n` at
which `[n]∗F(W)` is separably closed below and at every `n` in characteristic zero"*.  What those
clauses name is `hsep` and the instance `[CharZero F]`, and neither derivation above runs from
either.  ⚠️ `[CharZero F]` does not derive the non-constancy in any case: `xCoord_zero` makes `h`
false at `n = 0` in every characteristic, so *"at every `n` in characteristic zero"* is not true
on its own terms.  ⚠️ **Those three were short, and the second ground offered for them does not
hold either** (`#1668`).  This paragraph closed *"**Those three are cleared by the register and
not by the exemption** — they are not silently short, because the sentence opening this section
tells the reader they bind `h`; what was wrong is the ground.  The clearance is real; that wording
of it was not"* (`5dfd94d`, `#1658`, PR #664).  There is no register for them to be cleared by:
the sentence that wording names heads another `##` section, and `README.md`
`### Module-block bullets` binds a reach register to *"the list it heads"*.  False rather than
partial, so `### Retired claims` binds and the wording is quoted here.  **What replaces it is the
repair** — both bullets now name the non-constancy in the row, in the wording those declarations'
own headlines already use.  ⚠️ **In the row and not as a head-of-list register**, because two
bullets of the eleven were short and not eleven: `README.md` calls the `DeterminantModGeneral`
opener *"the cheap repair for a list whose bullets are **each** short of the same hypotheses"*,
and a register saying every statement below takes the non-constancy would be false of
`sum_ramificationIdxN_mul_residueDegreeN_two` and `…_three`, which derive it (`#1636`).
⚠️ Several further rows below make no claim about which `n` are reached at
all — `finrank_mulByNEndoFieldRange_of_smooth`, the integral-closure pair at the ring level, and
`placeBelowN` with its instances — and those are compliant on `### Reach clauses`' *"or it names
none"* branch, which is a third ground again and needs neither of the two above.

⚠️ **The sentence opening this section closed *"and no clause below repeats it"* until PR #671
rewrote it, and clauses below repeat it** (`5dfd94d`, `#1658`, PR #664).  It was false rather
than partial, so `README.md` `### Retired claims` binds and the wording is quoted here rather
than deleted.  ⚠️ **And its
replacement is retired in its turn by the repair above** (`#1668`): PR #671 put *"what replaced it
is the `## Main results` scope above, which holds — no bullet of that list names the
non-constancy"* in its place (`1354e2d`, `#1669`), and two bullets of that list now name it.  A
claim about the bullets is repaired where the bullets are; what replaces it is the count below,
which is over the **clauses** and does not quantify over the list.  Recogniser, published beside
the count as `### Module-block bullets` asks: every prose occurrence of *"non-constan…"* at or
below `## Main results`, read one by one.  **Thirteen** occur; two are the general
*"`deg φ = [F(W) : φ∗F(W)]` for non-constant `φ`"* fact about maps rather than a clause about a
declaration here, and eleven are clauses.  A second pass for the same
parameter named in other words adds one, the `_of_ne_zero` family's *"The transcendence proof is a
parameter of these statements"*.  ⚠️ **Backticked `transcendental_…` names are citations and not
clauses**, and are excluded; a recogniser that counts them reads this file as carrying dozens.

The twelve, because a count with no list under it is not checkable: the two `## Main results`
bullets repaired above, `isSeparable_mulByNEndoFieldRange_of_charZero`'s and
`sum_ramificationIdxN_mul_residueDegreeN_finrank` / `…_finrank_of_charZero`'s; the headlines of
**all three** of those declarations, the third since `#1664` below; the docstring bodies of
`…_finrank_of_charZero` — its headline and its body are two clauses, not one entry counted
twice — and `…_of_charZero_of_ne_zero`; the `_of_ne_zero` family's section
sentence; three sentences of `### Non-vacuity`; and the `### The relative residue degree`
block's gloss on `residueDegreeN_none_eq_one`.  ⚠️ **The last of those is about a declaration this
file imports, and it counts anyway** — *"A reach clause is answerable in the file that writes it,
wherever the declaration lives"* is this file's own ruling, written in that same block, so
*"below"* is positional and not a claim about where a cited declaration lives.  The verdict does not
turn on that reading: the other eleven are declarations of this file.

⚠️ **That census has moved again, and the figures it replaces are quoted rather than
overwritten.**  It read *"**Twelve** occur; … and ten are clauses"*, over a list headed
*"The eleven"* (`365dd39`, `#1668`, PR #683), and `#1664` falsified both figures and the list.  The
row that moved is `…_finrank_of_charZero`: its headline read *"in characteristic zero, at every
`n`"* and named the parameter only in its body — which is the entry the list already carried — and
`README.md` `### Scope of the rules above` rules that a sentence lower in a declaration's own
docstring does **not** repair its headline, the clause being where the reader meets it.  So the
headline now carries *"at every `n` at which `[n]` is non-constant"*, the wording its two siblings
already use, and the body clause stays.  False rather than partial, so `README.md`
`### Retired claims` binds: the figures are quoted here rather than deleted, and the live ones
above are stated **with the list of twelve printed in full**, because *"a count with no list under
it is not checkable"* is that census's own rule and a list told only that it gains an entry is the
state that rule forbids.

⚠️ **Every other numeral in this section is arithmetic on that census and moves with it in
place.**  The opening sentence's *"twelve clauses … three of them declaration headlines"*, *"the
other eleven are declarations of this file"* above, and *"the twelve listed above … the three
headlines"* and *"three of the twelve"* below are all read off the list; none of them is a claim
the census does not already make, which is why they are restated rather than quoted one by one.
⚠️ The census itself is the exception because it publishes its own recogniser and its own list, so
it is the sentence a reader quotes.

⚠️ **That same sentence carried a second universal, older and wider than the one above, and the
section heading restated it** (`#1688`).  Until now it read *"… as an explicit argument, and no
reach clause names it"*, under the heading *"⚠️ The transcendence parameter, and why no reach
clause below names it"* — both written by `01f955b` (`#1137`, PR #614), which predates PR #664's
appended clause and quantifies over a strictly wider unit than a bullet: `README.md`
`### Reach clauses` defines a reach clause as *"a docstring phrase that says how far a named
declaration or a named layer goes"*, and `### Scope of the rules above` makes a declaration
headline one.  **So the twelve listed above are twelve reach clauses that name it**, and the three
headlines among them settle it without the other nine.  ⚠️ **It was false on the day it landed**:
both of those headlines already read *"at every `n` at which `[n]` is non-constant"* at `01f955b`
itself.  False rather than partial, so `README.md` `### Retired claims` binds and both wordings are
quoted here rather than deleted.  What replaced the clause is the subset claim in this section's
opening sentence, naming those two and pointing at this list for the rest; what replaced the
heading is a title that asks **which** clauses below name the parameter instead of asserting that
none do.
⚠️ **The heading is the half that had to go first.**  doc-gen prints it as the section title, it is
the one sentence here that no later paragraph qualifies, and a reader who reads nothing else in
this section reads it.  ⚠️ **`#1668` has since decided which list this section's opening sentence
binds, and the answer is none** — it heads no list.  The replacement claim survives that ruling
because it is about the **clauses**; *"no bullet of `## Main results` repeats it"*, which was about
the list, did not.

⚠️ **`isSeparable_mulByNEndoFieldRange_of_charZero`,
`sum_ramificationIdxN_mul_residueDegreeN_finrank` and `…_finrank_of_charZero` answer for their
headlines in a different block, and a headline clears no bullet.**  `README.md`
`### Module-block bullets`: *"The traffic runs one way.  A block repairs a bullet; a bullet repairs
nothing … a module list and the file's headlines are two blocks … and the two layers are repaired
separately."*  So the verdict on those two bullets is a claim about the bullets, and what those
three headlines say neither strengthened nor weakened it — which is why the headlines did not spare
the bullets the repair above.  Recorded because three of the twelve clauses listed above are
headlines of these three, and all three now name the non-constancy in the headline itself.
⚠️ **`…_finrank_of_charZero`'s did not until `#1664`, and this paragraph is where that was
recorded** (`1354e2d`, `#1669`, PR #671).  It read *"and `…_finrank_of_charZero`'s does not"*, of a
headline reading *"in characteristic zero, at every `n`"* and naming the non-constancy a line lower
in the same docstring, and it closed *"A `#1664` candidate, recorded and not repaired here: that
issue is the headline block, and the elaborated read it asks of every row is owed there"*.  That
arrangement is the one `README.md`'s *"Nor does a sentence lower in the declaration's own
docstring"* (`#1660`) rules does not repair a headline, which is why it was recorded; the read is
now done and the headline repaired, so both sentences are false rather than partial and
`### Retired claims` binds — quoted here rather than deleted.  What replaced them is the headline
naming the non-constancy, with the body clause left standing.

## Main results

⚠️ Every public declaration of this file is listed, and all are in namespace
`WeierstrassCurve.Affine.CoordinateRing`.  ⚠️ `residueDegreeN` itself is **not** among them: it,
its tower formula, `residueDegreeN_none_eq_one` and the consistency pair `residueDegreeN_two` /
`residueDegreeN_three` are `EllipticCurves.FunctionField.MulByNResidueDegree` (`#1225`), and this
file consumes them rather than restating them.

* `placeBelowN`, with its `IsDiscreteValuationRing` and `Module.IsTorsionFree` instances, and
  `placeBelowN_comapProjPointN` — the place of `[n]∗F(W)` below `q`;
* `finrank_mulByNEndoFieldRange_of_smooth` — `[F(W) : [n]∗F(W)] = n²` in the `Subfield`
  presentation.  ⚠️ **No `[IsAlgClosed F]`**: this is `#1213`'s degree, which needs none;
* `isSeparable_mulByNEndoFieldRange_of_charZero` — separability in characteristic zero at
  **every** `n` at which `[n]` is non-constant, the general-`n` form of the merged
  `isSeparable_mulByTwoEndoFieldRange`.  ⚠️ Incomparable with `#1219`'s: neither `[CharZero F]` nor
  `[IsAlgClosed F]` implies the other, and this one is not restricted to `3`-smooth `n`;
* `module_finite_integralClosure_placeBelowN_of_isSeparable` and
  `finrank_integralClosure_placeBelowN_of_smooth` — the right-hand side at the ring level;
* **`sum_ramificationIdxN_mul_residueDegreeN_finrank`** and
  **`…_finrank_of_charZero`** — **the identity**, `∑_{p ↦ q} e_p · f_p = [F(W) : [n]∗F(W)]`, at
  every `n` at which `[n]` is non-constant: the first with `[n]∗F(W)` separably closed below, the
  second in characteristic zero;
* **`sum_ramificationIdxN_mul_residueDegreeN_of_isSeparable`**, **`…_of_smooth`** and
  **`…_of_charZero`** — the same with the right-hand side evaluated, `= n ^ 2`, at every
  `3`-smooth `n ≠ 0` with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`;
* ⚠️ `finrank_mulByNEndoFieldRange_of_ne_zero`, `finrank_integralClosure_placeBelowN_of_ne_zero`,
  `sum_ramificationIdxN_mul_residueDegreeN_of_isSeparable_of_ne_zero`,
  `sum_ramificationIdxN_mul_residueDegreeN_of_ne_zero`,
  `sum_ramificationIdxN_mul_residueDegreeN_of_charZero_of_ne_zero` and
  `sum_ramificationIdxN_of_ne_zero` — **the same six statements as their `_of_smooth` siblings, at
  every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`** (`#1523` item 4), with
  `finrank_integralClosure_placeBelowN_of_ne_zero` and
  `sum_ramificationIdxN_mul_residueDegreeN_of_isSeparable_of_ne_zero` **carrying separability as a
  hypothesis besides**, as their own headlines say and the other four do not.  The two substituted
  inputs are `#1213`'s general degree and `#1523`'s general separability; no new argument.
  ⚠️ **That is an input to those proofs and not a discharge of `hsep` across the six** (`#1665`):
  `finrank_mulByNEndoFieldRange_of_ne_zero` needs no separability at all, and the other three
  discharge it from an instance they carry — `isSeparable_mulByNEndoFieldRange_of_ne_zero`
  (`EllipticCurves.FunctionField.MulByNGalois`) under `[IsAlgClosed F]` and
  `isSeparable_mulByNEndoFieldRange_of_charZero` above under `[CharZero F]` — neither of which the
  two named with it carry, so the `README.md` derivability exemption does not reach them.
* `finrank_mulByNEndoFieldRange_five`, `sum_ramificationIdxN_mul_residueDegreeN_five` and
  `sum_ramificationIdxN_five` — the first index outside `{2, 3}`, named rather than left as
  `example`s.
* `sum_ramificationIdxN_of_smooth` — the collapsed form `∑_{p ↦ q} e_p = n²` over `F̄`, at every
  `3`-smooth `n ≠ 0` with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, the general-`n` shape of
  `sum_ramificationIdxTwo_eq_four` and `sum_ramificationIdxThree_eq_nine`;
* `sum_ramificationIdxN_mul_residueDegreeN_two` and `…_three` — the sum-level consistency with the
  two merged instantiations;
* **`sum_ramificationIdxThree_mul_residueDegreeThree_of_charZero`** — `∑_{p ↦ q} e_p · f_p = 9` in
  the `[3]`-indexing with **no `[IsAlgClosed F]`**, which `MulByThreeResidueDegree` names as what is
  still absent.

## ⚠️ What this does *not* give

* **Not `#E[n] = n²`.**  `EllipticCurves.FunctionField.PlaceRamificationInertia`,
  `EllipticCurves.FunctionField.PlacePullback` and
  `EllipticCurves.FunctionField.MulByTwoFibreInfinity` all record that the counting step *"a
  separable isogeny has as many points in its kernel as its degree"* is nowhere in this tree.
  Widening the fundamental identity does not add it.  What is counted below is **places of `F(W)`
  in a fibre**, weighted by ramification and residue degree; the passage to points is a different
  theorem.
* ⚠️ **`n = 5` IS here now, and this bullet is what changed.**  It used to say *"nothing at
  `n = 5` with the value `n²`, because `#1213`'s degree stops there"* — a reason that was already
  false when the file was written, since `finrank_mulByNFieldRange_eq_sq_of_two_ne_zero`
  (`EllipticCurves.FunctionField.MulByNDegreeGeneral`) has been `[F(W) : [n]∗F(W)] = n²` at every
  `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` since PR #576.  ⚠️ That one is the **`ℤ`** cast —
  its `_of_two_ne_zero` suffix names the hypothesis this file's own six state as `(n : F) ≠ 0`.
  `#1523` item 4 is what rewrote the statements onto it:
  `finrank_mulByNEndoFieldRange_of_ne_zero`, `finrank_integralClosure_placeBelowN_of_ne_zero`,
  `sum_ramificationIdxN_mul_residueDegreeN_of_isSeparable_of_ne_zero`, `…_of_ne_zero`,
  `…_of_charZero_of_ne_zero` and `sum_ramificationIdxN_of_ne_zero` are the same six statements at
  every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`, and `sum_ramificationIdxN_five` evaluates the
  right-hand side at `5`.  ⚠️ The `_of_smooth` forms are **kept** and are not deprecated: they are
  the only route here
  that does not consume `#E[n] = n²`.
* **Still nothing at `n = char F`, and the gate there is separability, not the degree.**
  `(n : F) ≠ 0` is sharp for the statements below, and the reason is the one
  `EllipticCurves.FunctionField.MulByNGalois` already gives: at `p = char F` the *count*
  `#E[p] = p²` is false (`E[p]` is `0` or `ℤ/pℤ`, never `(ℤ/pℤ)²`), and `[p]` is inseparable, so
  every `hsep` hypothesis below fails.  ⚠️ **Do not read that as "the degree fails there".**
  `deg[n] = n²` holds over a field of any characteristic and `deg φ = [F(W) : φ∗F(W)]` for any
  non-constant `φ`, so `[F(W) : [p]∗F(W)] = p²` is *true* at `p = char F`; what
  `EllipticCurves.FunctionField.MulByNDegreeGeneral` says of itself is the accurate thing — in
  characteristic `p` at `p ∣ n` **that file's proof** says nothing, its `(n : F) ≠ 0` coming from
  `natDegree_ΨSq` and the transcendence input rather than from the truth of the statement.
  Inseparability is a split of `p²` into `deg_s · deg_i`, not a drop in it.
* ⚠️ **`n = char F` is the wrong witness for *"the identity is wider than the value"*, and this
  bullet used to name it as one.**  `sum_ramificationIdxN_mul_residueDegreeN_finrank` carries no
  hypothesis on `n` — but it carries `hsep`, which is precisely what fails at `n = char F`, so it
  is *vacuous* there rather than wider.  The distinction is real, and its witness is the `n = 5`
  certificate below, which commits `sum_ramificationIdxN_mul_residueDegreeN_finrank_of_charZero`:
  no hypothesis on `n` there either, and in characteristic zero no separability hypothesis to
  fail, with the right-hand side left as a `finrank` rather than evaluated.
* **Not `hprin`** (`#962`).  `PlaceInertiaGeneral`'s `## Scope` records that it removes one of three
  `[IsAlgClosed F]` inputs to `exists_nsmul_divisor_eq_divisor_mulByTwoEndo` and not the other two;
  that accounting is unchanged at general `n`, and nothing below touches `card_torsion_two` or
  `exists_nsmul_two_eq`.
* **No value for any individual `e_p` or `f_p`.**  `ramificationIdxN_none_of_ne_zero`
  (`MulByNPlaceComposition`, PR #599) gives `e_∞ = 1` at every `n` with `(2 : F) ≠ 0` and
  `((n : ℤ) : F) ≠ 0` — and `ramificationIdxN_none_of_smooth` beside it by the independent
  `3`-smooth route — while `residueDegreeN_none_eq_one` (`MulByNResidueDegree`) gives `f_∞ = 1`; at
  every other place both are left as they are, exactly as at `n = 2`.  ⚠️ This bullet used to name
  only the `_of_smooth` form, which was sharp when written and stopped being so at PR #599.
* **No place with `f_p > 1` exhibited.**  As `PlaceInertiaGeneral` says of itself: the
  characteristic-zero statements are strictly stronger than their `[IsAlgClosed F]` siblings
  because they *apply* over a field that is not algebraically closed, which is what the certificate
  below shows; producing a closed point of degree `2` on a named curve is a different piece of work.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, III.1.11.
-/

open Module IsDedekindDomain

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]

/-! ### The relative residue degree of `[n]∗`

⚠️ Not defined here.  `residueDegreeN`, its tower formula
`residueDegreeProj_mul_residueDegreeN`, `residueDegreeN_none_eq_one` (`f_∞ = 1`, at every `n` at
which `[n]` is non-constant) and the consistency pair `residueDegreeN_two` /
`residueDegreeN_three` are `EllipticCurves.FunctionField.MulByNResidueDegree` (`#1225`), which
this file imports; the `φ`-congruence they are proved by is `residueDegreeComap_congr`
(`EllipticCurves.FunctionField.PlaceResidueComap`).  Everything below consumes them.

⚠️ **The index clause is quoted from the defining module, not paraphrased** (`#1652`).  It read
*"`f_∞ = 1` at every `n`"* here from `4a30e82` (`#1221`) until now; PR #653 (`#1636`) repaired
that same claim where the declaration lives, because `residueDegreeN_none_eq_one` binds
`hn : Transcendental F (n • genericPoint).xCoord` and `xCoord_zero` makes it false at `n = 0`, so
a clause naming the index range and not `hn` is the omission `README.md` `### Reach clauses`
convicts by name in `ramificationIdxN_pos` — over the same binder in the same argument position.
⚠️ **A reach clause is answerable in the file that writes it**, wherever the declaration lives: a
repaired bullet and a register at the head of a `## Main *` list sit in the defining module's own
docstring and reach that list, so a fortiori they do not reach a sentence in an importing file, and
a citation restating an imported statement's reach names that statement's whole hypothesis list
itself or names none of it.  `README.md` `### Module-block bullets`' *"The traffic runs one way"*
is the in-file form of the same direction. -/

namespace CoordinateRing

variable [W.IsElliptic]

/-! ### The place of `[n]∗F(W)` below a place of `F(W)` -/

variable (W) in
/-- **The valuation ring of the place of `[n]∗F(W)` below `q`.**  The `[n]∗` instantiation of
`placeBelow` (`#754`), and the general-`n` form of the merged `placeBelowTwo` and
`placeBelowThree`. -/
noncomputable def placeBelowN (n : ℕ)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (q : ProjPoint W) :
    ValuationSubring ↥(mulByNEndo n h).fieldRange :=
  placeBelow (mulByNEndo n h) q

/-- **A place of `[n]∗F(W)` is a discrete valuation ring.**  Restated at the `[n]∗` layer for the
reason `placeBelowTwo` restates it: `placeBelowN` is a `def` rather than an `abbrev`, so search
does not see through it to the general instance.  `IsNoetherianRing` and `IsPrincipalIdealRing`
follow from this one. -/
instance instIsDiscreteValuationRingPlaceBelowN (n : ℕ)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (q : ProjPoint W) :
    IsDiscreteValuationRing ↥(placeBelowN W n h q) :=
  instIsDiscreteValuationRingPlaceBelow q

/-- **`F(W)` is torsion-free over a place of `[n]∗F(W)`**, restated at the `[n]∗` layer for the same
reason. -/
instance instIsTorsionFreePlaceBelowN (n : ℕ)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (q : ProjPoint W) :
    Module.IsTorsionFree ↥(placeBelowN W n h q) W.FunctionField :=
  instIsTorsionFreePlaceBelow q

/-- **The place of `[n]∗F(W)` below `p` is `[n]∗F(W) ∩ placeOf W p`**, the classical description.
The `[n]∗` form of `placeBelow_comapProjPoint`. -/
theorem placeBelowN_comapProjPointN (n : ℕ)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (p : ProjPoint W) :
    placeBelowN W n h (comapProjPointN n h p)
      = (placeOf W p).comap ((mulByNEndo n h).fieldRange.subtype) :=
  placeBelow_comapProjPoint _ _ p

/-! ### The two hypotheses of the identity, at `[n]∗` -/

omit [IsDedekindDomain W.CoordinateRing] in
/-- **`[F(W) : [n]∗F(W)] = n²` at every `3`-smooth `n ≠ 0` with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`,
for the subfield.**
`finrank_mulByNFieldRange_of_smooth` (`#1213`) in the `Subfield` presentation the place machinery
needs, crossed along `#1219`'s `mulByNFieldRangeEquivSubfield`.

⚠️ **No `[IsAlgClosed F]` and no separability.**  This is the degree, which needs neither; only the
statements below it that consume `Algebra.IsSeparable` do.  The general-`n` form of the merged
`finrank_mulByTwoEndoFieldRange` and `finrank_mulByThreeEndoFieldRange`, and their proof verbatim
with a different equiv. -/
theorem finrank_mulByNEndoFieldRange_of_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    finrank ↥(mulByNEndo n h).fieldRange W.FunctionField = n ^ 2 := by
  rw [← Algebra.finrank_eq_of_equiv_equiv (mulByNFieldRangeEquivSubfield n h)
    (RingEquiv.refl W.FunctionField) (by ext a; rfl)]
  exact finrank_mulByNFieldRange_of_smooth h2 h3 hn hfac h

omit [IsDedekindDomain W.CoordinateRing] in
/-- **In characteristic zero, `F(W)` is separable over `[n]∗F(W)` at every `n` at which `[n]` is
non-constant.**

The extension is finite (`module_finite_mulByNEndoFieldRange`, general `n`), hence integral, and
`Algebra.IsSeparable.of_integral` is an instance over a characteristic-zero base.  `CharZero` is
transported twice, from `F` to `F(W)` along the injective structure map and from `F(W)` down to the
subfield — the merged `isSeparable_mulByTwoEndoFieldRange` verbatim, with `n` in place of `2`.

⚠️ **This is not weaker than `#1219`'s `isSeparable_mulByNEndoFieldRange_of_smooth`, and not
stronger: the two are incomparable.**  `[CharZero F]` and `[IsAlgClosed F]` neither implies the
other, as `#754` records; but this one carries **no `3`-smoothness**, because it never touches the
composition law — so in characteristic zero the separability, and with it the fundamental identity,
holds at every `n`, `n = 5` included.  What remains `3`-smooth there is only the *value* `n²`. -/
theorem isSeparable_mulByNEndoFieldRange_of_charZero [CharZero F] (n : ℕ)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    Algebra.IsSeparable ↥(mulByNEndo n h).fieldRange W.FunctionField := by
  haveI : CharZero W.FunctionField :=
    charZero_of_injective_algebraMap (algebraMap F W.FunctionField).injective
  haveI : CharZero ↥(mulByNEndo n h).fieldRange :=
    ((mulByNEndo n h).fieldRange.subtype).charZero
  haveI := module_finite_mulByNEndoFieldRange n h
  haveI : Algebra.IsIntegral ↥(mulByNEndo n h).fieldRange W.FunctionField :=
    Algebra.IsIntegral.of_finite _ _
  infer_instance

/-! ### The right-hand side, at the ring level -/

/-- **The integral closure of a place of `[n]∗F(W)` is module-finite over it**, given separability.
`IsIntegralClosure.finite` through `module_finite_integralClosure_placeBelow` (`#754`), with
`Module.Finite` of the field extension supplied at **general** `n`. -/
theorem module_finite_integralClosure_placeBelowN_of_isSeparable (n : ℕ)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hsep : Algebra.IsSeparable ↥(mulByNEndo n h).fieldRange W.FunctionField)
    (q : ProjPoint W) :
    Module.Finite ↥(placeBelowN W n h q)
      ↥(integralClosure ↥(placeBelowN W n h q) W.FunctionField) := by
  haveI := module_finite_mulByNEndoFieldRange n h
  haveI := hsep
  exact module_finite_integralClosure_placeBelow q

/-- **The integral closure of a place of `[n]∗F(W)` has rank `n²` over it** at every `3`-smooth
`n ≠ 0` with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, given separability — the right-hand side of the
fundamental identity at the ring level, so
that the identity below never descends from the field degree by hand.

The general-`n` form of `finrank_integralClosure_placeBelowTwo` and
`finrank_integralClosure_placeBelowThree`. -/
theorem finrank_integralClosure_placeBelowN_of_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hsep : Algebra.IsSeparable ↥(mulByNEndo n h).fieldRange W.FunctionField)
    (q : ProjPoint W) :
    finrank ↥(placeBelowN W n h q)
      ↥(integralClosure ↥(placeBelowN W n h q) W.FunctionField) = n ^ 2 := by
  haveI := module_finite_mulByNEndoFieldRange n h
  haveI := hsep
  exact (finrank_integralClosure_placeBelow (φ := mulByNEndo n h) q).trans
    (finrank_mulByNEndoFieldRange_of_smooth h2 h3 hn hfac h)

/-! ### The fundamental identity

⚠️ The two statements in this section are the theorems; everything in the next one is a corollary at
the indices where `[F(W) : [n]∗F(W)]` is known.  See the module docstring. -/

/-- **`∑_{p ↦ q} e_p · f_p = [F(W) : [n]∗F(W)]` for `[n]∗`, over an arbitrary field**, at every `n`
at which `[n]` is non-constant, with separability carried as a hypothesis exactly as `#754` carries
it.

⚠️ **No `3`-smoothness anywhere in this statement.**  What `3`-smoothness buys is the *value* of the
right-hand side, and that is the next section. -/
theorem sum_ramificationIdxN_mul_residueDegreeN_finrank (n : ℕ)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hsep : Algebra.IsSeparable ↥(mulByNEndo n h).fieldRange W.FunctionField)
    (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointN_preimage_singleton n h q).toFinset,
        (ramificationIdxN n h p).toNat * residueDegreeN n h p
      = finrank ↥(mulByNEndo n h).fieldRange W.FunctionField := by
  haveI := module_finite_mulByNEndoFieldRange n h
  haveI := hsep
  rw [← finrank_integralClosure_placeBelow (φ := mulByNEndo n h) q]
  exact sum_toNat_ramificationIdx_mul_residueDegreeComap_fibre
    (mulByNEndo_algebraMap_base n h) (mulByNEndo_isIntegralElem n h)

/-- **`∑_{p ↦ q} e_p · f_p = [F(W) : [n]∗F(W)]` in characteristic zero, at every `n` at which
`[n]` is non-constant.**

The widest statement in this file: over `ℚ`, or any characteristic-zero field, the fundamental
identity for `[n]∗` holds at **every** `n` at which `[n]` is non-constant — no `3`-smoothness, no
algebraic closure, `n = 5` included.  Separability is discharged by
`isSeparable_mulByNEndoFieldRange_of_charZero`.

⚠️ The right-hand side cannot be evaluated at a general `n`: `[F(W) : [n]∗F(W)] = n²` is `#1213`,
which stops at `3`-smooth `n`.  Leaving it as a `finrank` is what makes the statement true at every
`n`, and replacing it by `n ^ 2` would be a *narrower* theorem, not a sharper one. -/
theorem sum_ramificationIdxN_mul_residueDegreeN_finrank_of_charZero [CharZero F] (n : ℕ)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointN_preimage_singleton n h q).toFinset,
        (ramificationIdxN n h p).toNat * residueDegreeN n h p
      = finrank ↥(mulByNEndo n h).fieldRange W.FunctionField :=
  sum_ramificationIdxN_mul_residueDegreeN_finrank n h
    (isSeparable_mulByNEndoFieldRange_of_charZero n h) q

/-! ### The right-hand side evaluated: `= n²` at every `3`-smooth `n` -/

/-- **`∑_{p ↦ q} e_p · f_p = n²` for `[n]∗` at every `3`-smooth `n ≠ 0` with `(2 : F) ≠ 0` and
`(3 : F) ≠ 0`, over an arbitrary field**, with separability carried as a hypothesis.

The general-`n` form of `sum_ramificationIdxTwo_mul_residueDegreeTwo_of_isSeparable`
(`EllipticCurves.FunctionField.PlaceInertiaGeneral`).  ⚠️ It does **not** say `#E[n] = n²`: what is
counted is places of `F(W)` in a fibre, and the passage to points needs the separable-isogeny count
this tree does not have.  See the module docstring. -/
theorem sum_ramificationIdxN_mul_residueDegreeN_of_isSeparable (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hsep : Algebra.IsSeparable ↥(mulByNEndo n h).fieldRange W.FunctionField)
    (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointN_preimage_singleton n h q).toFinset,
      (ramificationIdxN n h p).toNat * residueDegreeN n h p = n ^ 2 :=
  (sum_ramificationIdxN_mul_residueDegreeN_finrank n h hsep q).trans
    (finrank_mulByNEndoFieldRange_of_smooth h2 h3 hn hfac h)

/-- **`∑_{p ↦ q} e_p · f_p = n²` at every `3`-smooth `n ≠ 0` with `(2 : F) ≠ 0` and
`(3 : F) ≠ 0`, over `F̄`** — separability discharged by `#1219`.  This is what `#1221` was filed
for. -/
theorem sum_ramificationIdxN_mul_residueDegreeN_of_smooth [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointN_preimage_singleton n h q).toFinset,
      (ramificationIdxN n h p).toNat * residueDegreeN n h p = n ^ 2 :=
  sum_ramificationIdxN_mul_residueDegreeN_of_isSeparable h2 h3 hn hfac h
    (isSeparable_mulByNEndoFieldRange_of_smooth h2 h3 hn hfac h) q

/-- **`∑_{p ↦ q} e_p · f_p = n²` at every `3`-smooth `n ≠ 0` with `(2 : F) ≠ 0` and
`(3 : F) ≠ 0`, in characteristic zero** — the form available over `ℚ`, where
`sum_ramificationIdxN_of_smooth` is not. -/
theorem sum_ramificationIdxN_mul_residueDegreeN_of_charZero [CharZero F] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointN_preimage_singleton n h q).toFinset,
      (ramificationIdxN n h p).toNat * residueDegreeN n h p = n ^ 2 :=
  sum_ramificationIdxN_mul_residueDegreeN_of_isSeparable h2 h3 hn hfac h
    (isSeparable_mulByNEndoFieldRange_of_charZero n h) q

/-- **The collapsed form `∑_{p ↦ q} e_p = n²` over `F̄`**, at every `3`-smooth `n ≠ 0` with
`(2 : F) ≠ 0` and `(3 : F) ≠ 0`.

Over an algebraically closed base field every place is rational, so every `f_p` is `1`.  The
general-`n` shape of `sum_ramificationIdxTwo_eq_four`
(`EllipticCurves.FunctionField.PlaceRamificationInertia`) and `sum_ramificationIdxThree_eq_nine`
(`EllipticCurves.FunctionField.MulByThreeRamification`), neither of which had a general-`n` form.

⚠️ `[IsAlgClosed F]` is **not** removable here, and not merely unproved: `residueDegreeProj_eq_one`
is equivalent to the base field being algebraically closed, and over `ℚ` the statement is false
as soon as some place in the fibre has residue degree `2`.  The weighted form above is what
generalises; see `PlaceInertiaGeneral`'s docstring on exactly this point. -/
theorem sum_ramificationIdxN_of_smooth [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointN_preimage_singleton n h q).toFinset,
      (ramificationIdxN n h p).toNat = n ^ 2 := by
  rw [← sum_ramificationIdxN_mul_residueDegreeN_of_smooth h2 h3 hn hfac h q]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [residueDegreeN_eq_one_of_residueDegreeProj_eq_one n h (residueDegreeProj_eq_one p), mul_one]

/-! ### The same chain at every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`

⚠️ **The `3`-smoothness above was never in the mathematics of this file; it was in the two names the
chain cites.**  Both have general replacements on `main`:

* the degree — `finrank_mulByNFieldRange_eq_sq_of_two_ne_zero`
  (`EllipticCurves.FunctionField.MulByNDegreeGeneral`, `#1213`), `[F(W) : [n]∗F(W)] = n²` at every
  `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`, no smoothness and no algebraic closure;
* separability — `isSeparable_mulByNEndoFieldRange_of_ne_zero`
  (`EllipticCurves.FunctionField.MulByNGalois`, `#1523` items 1-3), off the fixed field of `E[n]`
  rather than off a composition ladder.

So the six statements below are the six above with those two inputs substituted and **no new
argument**.  ⚠️ The `_of_smooth` forms are **kept**, not replaced: they are what `TwoPrimary` and
`ThreePrimary` consumers cite, and they remain the only route here that does not consume
`#E[n] = n²`.

⚠️ **The transcendence proof is a parameter of these statements and is fixed inside
`finrank_mulByNFieldRange_eq_sq_of_two_ne_zero`.**  `Transcendental` is a `Prop` and proof
irrelevance is definitional in Lean 4, so the two subfields are the same and no `Subsingleton.elim`
is needed; `MulByNDegreeGeneral` records the same trap.

⚠️ `(n : F) ≠ 0` is **sharp** and is not a relaxed smoothness — and the sharpness is
`EllipticCurves.FunctionField.MulByNGalois`'s, i.e. it is about the **count and separability**, not
about the degree.  At `p = char F` the map `[p]` is inseparable, so `hsep` fails and `#E[p] = p²`
fails with it, which is what stops the chain.  ⚠️ It is `[p]`, not `[n]`: at an `n` prime to `p` the
map `[n]` is separable in characteristic `p` too, and this sentence carried `[n]` until `#1523`
paid it off.  ⚠️ **The degree itself survives there**:
`deg[n] = n²` in every characteristic and `deg φ = [F(W) : φ∗F(W)]` for non-constant `φ`, so
`[F(W) : [p]∗F(W)] = p²` is true at `p = char F` — `MulByNDegreeGeneral` claims only that *its
proof* says nothing at `p ∣ n`, and that is the accurate claim to repeat. -/

omit [IsDedekindDomain W.CoordinateRing] in
/-- **`[F(W) : [n]∗F(W)] = n²` at every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`, for the
subfield.**  The general-`n` form of `finrank_mulByNEndoFieldRange_of_smooth`, crossed along
`#1219`'s `mulByNFieldRangeEquivSubfield` in exactly the same way.

⚠️ **No `[IsAlgClosed F]`, no separability and no smoothness.**  This is the degree, and `#1213`'s
general form needs none of the three. -/
theorem finrank_mulByNEndoFieldRange_of_ne_zero (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : (n : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    finrank ↥(mulByNEndo n h).fieldRange W.FunctionField = n ^ 2 := by
  rw [← Algebra.finrank_eq_of_equiv_equiv (mulByNFieldRangeEquivSubfield n h)
    (RingEquiv.refl W.FunctionField) (by ext a; rfl)]
  exact finrank_mulByNFieldRange_eq_sq_of_two_ne_zero h2 (by exact_mod_cast hn)

/-- **The integral closure of a place of `[n]∗F(W)` has rank `n²` over it** at every `n` with
`(2 : F) ≠ 0` and `(n : F) ≠ 0`, given separability — the right-hand side of the fundamental
identity at the ring level.  The general-`n` form of
`finrank_integralClosure_placeBelowN_of_smooth`. -/
theorem finrank_integralClosure_placeBelowN_of_ne_zero (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : (n : F) ≠ 0) (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hsep : Algebra.IsSeparable ↥(mulByNEndo n h).fieldRange W.FunctionField) (q : ProjPoint W) :
    finrank ↥(placeBelowN W n h q)
      ↥(integralClosure ↥(placeBelowN W n h q) W.FunctionField) = n ^ 2 := by
  haveI := module_finite_mulByNEndoFieldRange n h
  haveI := hsep
  exact (finrank_integralClosure_placeBelow (φ := mulByNEndo n h) q).trans
    (finrank_mulByNEndoFieldRange_of_ne_zero h2 hn h)

/-- **`∑_{p ↦ q} e_p · f_p = n²` for `[n]∗` at every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`, over
an arbitrary field**, with separability carried as a hypothesis.  The general-`n` form of
`sum_ramificationIdxN_mul_residueDegreeN_of_isSeparable`.

⚠️ It does **not** say `#E[n] = n²`: what is counted is places of `F(W)` in a fibre, and the passage
to points needs the separable-isogeny count this tree does not have.  Lifting the index range
changes nothing about that; see the module docstring. -/
theorem sum_ramificationIdxN_mul_residueDegreeN_of_isSeparable_of_ne_zero (h2 : (2 : F) ≠ 0)
    {n : ℕ} (hn : (n : F) ≠ 0) (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hsep : Algebra.IsSeparable ↥(mulByNEndo n h).fieldRange W.FunctionField) (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointN_preimage_singleton n h q).toFinset,
      (ramificationIdxN n h p).toNat * residueDegreeN n h p = n ^ 2 :=
  (sum_ramificationIdxN_mul_residueDegreeN_finrank n h hsep q).trans
    (finrank_mulByNEndoFieldRange_of_ne_zero h2 hn h)

/-- **`∑_{p ↦ q} e_p · f_p = n²` at every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`, over `F̄`** —
separability discharged by `isSeparable_mulByNEndoFieldRange_of_ne_zero` rather than by `#1219`'s
`3`-smooth form.  The general-`n` form of
`sum_ramificationIdxN_mul_residueDegreeN_of_smooth`. -/
theorem sum_ramificationIdxN_mul_residueDegreeN_of_ne_zero [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    {n : ℕ} (hn : (n : F) ≠ 0) (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointN_preimage_singleton n h q).toFinset,
      (ramificationIdxN n h p).toNat * residueDegreeN n h p = n ^ 2 :=
  sum_ramificationIdxN_mul_residueDegreeN_of_isSeparable_of_ne_zero h2 hn h
    (isSeparable_mulByNEndoFieldRange_of_ne_zero h2 hn h) q

/-- **`∑_{p ↦ q} e_p · f_p = n²` at every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`, in
characteristic zero** — the form available over `ℚ`, where the `[IsAlgClosed F]` statement above is
not.

⚠️ In characteristic zero `(n : F) ≠ 0` is automatic for `n ≠ 0`, so this is the identity at every
non-constant index over `ℚ`; the hypothesis is kept in this shape only so that the statement reads
the same as its siblings. -/
theorem sum_ramificationIdxN_mul_residueDegreeN_of_charZero_of_ne_zero [CharZero F]
    (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : (n : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointN_preimage_singleton n h q).toFinset,
      (ramificationIdxN n h p).toNat * residueDegreeN n h p = n ^ 2 :=
  sum_ramificationIdxN_mul_residueDegreeN_of_isSeparable_of_ne_zero h2 hn h
    (isSeparable_mulByNEndoFieldRange_of_charZero n h) q

/-- **The collapsed form `∑_{p ↦ q} e_p = n²` over `F̄`**, at every `n` with `(2 : F) ≠ 0` and
`(n : F) ≠ 0`.  The general-`n` form of `sum_ramificationIdxN_of_smooth`, and the statement
`card_fibre_comapProjPointN_le_sq_of_ne_zero` (`EllipticCurves.FunctionField.MulByNFibre`)
consumes.

⚠️ `[IsAlgClosed F]` is **not** removable here and is not a gate that lifting the index range
touches: `residueDegreeProj_eq_one` is equivalent to the base field being algebraically closed, and
over `ℚ` the statement is false as soon as some place in the fibre has residue degree `2`.  The
weighted form above is what generalises. -/
theorem sum_ramificationIdxN_of_ne_zero [IsAlgClosed F] (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : (n : F) ≠ 0) (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointN_preimage_singleton n h q).toFinset,
      (ramificationIdxN n h p).toNat = n ^ 2 := by
  rw [← sum_ramificationIdxN_mul_residueDegreeN_of_ne_zero h2 hn h q]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [residueDegreeN_eq_one_of_residueDegreeProj_eq_one n h (residueDegreeProj_eq_one p), mul_one]

/-! ### `n = 5`, as named theorems

⚠️ This file's `n = 5` bullet used to give its reason as *"because `#1213`'s degree stops there"*,
which `#1523` items 1-3 corrected: the degree has not stopped there since PR #576.  The statements
below are the machine-checked consequence — named rather than left as `example`s so that a reader
can grep for them and a consumer can cite them.

`5` is the smallest index that is neither `3`-smooth nor covered by the merged `n = 2` / `n = 3`
packages, so a proof that reaches it cannot be any composition of those two.  ⚠️ Stated over an
arbitrary algebraically closed `F` with `(5 : F) ≠ 0`; the concrete instantiation on a committed
curve is in the non-vacuity section below. -/

omit [IsDedekindDomain W.CoordinateRing] in
/-- **`[F(W) : [5]∗F(W)] = 25`, in the `Subfield` presentation** — the degree at the first index
outside `{2, 3}`, in the shape the place machinery below consumes. -/
theorem finrank_mulByNEndoFieldRange_five (h2 : (2 : F) ≠ 0) (h5 : (5 : F) ≠ 0) :
    finrank ↥(mulByNEndo (W := W) 5
      (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2
        (by simpa using h5))).fieldRange W.FunctionField = 5 ^ 2 :=
  finrank_mulByNEndoFieldRange_of_ne_zero h2 (by exact_mod_cast h5) _

/-- **`∑_{p ↦ q} e_p · f_p = 25` for `[5]∗` over `F̄`** — the fundamental identity at an index no
`3`-smooth statement in this file reaches. -/
theorem sum_ramificationIdxN_mul_residueDegreeN_five [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    (h5 : (5 : F) ≠ 0) (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointN_preimage_singleton 5
        (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2
          (by simpa using h5)) q).toFinset,
      (ramificationIdxN 5 (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2
        (by simpa using h5)) p).toNat
        * residueDegreeN 5 (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2
          (by simpa using h5)) p = 5 ^ 2 :=
  sum_ramificationIdxN_mul_residueDegreeN_of_ne_zero h2 (by exact_mod_cast h5) _ q

/-- **The collapsed form `∑_{p ↦ q} e_p = 25` for `[5]∗` over `F̄`.** -/
theorem sum_ramificationIdxN_five [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h5 : (5 : F) ≠ 0)
    (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointN_preimage_singleton 5
        (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2
          (by simpa using h5)) q).toFinset,
      (ramificationIdxN 5 (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2
        (by simpa using h5)) p).toNat = 5 ^ 2 :=
  sum_ramificationIdxN_of_ne_zero h2 (by exact_mod_cast h5) _ q

/-! ### The identity is the merged one at `n = 2` and at `n = 3`

Stated as a check that nothing drifted between the `[n]`-indexing and the two merged
instantiations, and because a consumer holding an `n` cannot otherwise use them.  ⚠️ At `n = 3`
this is also the only bridge: `sum_ramificationIdxThree_mul_residueDegreeThree` carries
`[IsAlgClosed F]`, so the `_of_isSeparable` and `_of_charZero` forms above are new there. -/

/-- **At `n = 2` the identity is `sum_ramificationIdxTwo_mul_residueDegreeTwo`.**  The two fibres
are the same set by `comapProjPointN_two`, and the two summands agree by `ramificationIdxN_two` and
`residueDegreeN_two`. -/
theorem sum_ramificationIdxN_mul_residueDegreeN_two (h2 : (2 : F) ≠ 0) (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointN_preimage_singleton 2
        (transcendental_xCoord_two_nsmul (W := W) h2) q).toFinset,
        (ramificationIdxN 2 (transcendental_xCoord_two_nsmul (W := W) h2) p).toNat
          * residueDegreeN 2 (transcendental_xCoord_two_nsmul (W := W) h2) p
      = ∑ p ∈ (finite_comapProjPointTwo_preimage_singleton h2 q).toFinset,
        (ramificationIdxTwo h2 p).toNat * residueDegreeTwo h2 p := by
  have hset : (finite_comapProjPointN_preimage_singleton 2
      (transcendental_xCoord_two_nsmul (W := W) h2) q).toFinset
        = (finite_comapProjPointTwo_preimage_singleton h2 q).toFinset := by
    ext p
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff,
      comapProjPointN_two h2 p]
  rw [hset]
  exact Finset.sum_congr rfl fun p _ => by
    rw [ramificationIdxN_two h2 p, residueDegreeN_two h2 p]

/-- **At `n = 3` the identity is `sum_ramificationIdxThree_mul_residueDegreeThree`.**  The `n = 3`
mirror of the previous statement, through `comapProjPointN_three`, `ramificationIdxN_three` and
`residueDegreeN_three`. -/
theorem sum_ramificationIdxN_mul_residueDegreeN_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointN_preimage_singleton 3
        (transcendental_xCoord_three_nsmul (W := W) h2 h3) q).toFinset,
        (ramificationIdxN 3 (transcendental_xCoord_three_nsmul (W := W) h2 h3) p).toNat
          * residueDegreeN 3 (transcendental_xCoord_three_nsmul (W := W) h2 h3) p
      = ∑ p ∈ (finite_comapProjPointThree_preimage_singleton h2 h3 q).toFinset,
        (ramificationIdxThree h2 h3 p).toNat * residueDegreeThree h2 h3 p := by
  have hset : (finite_comapProjPointN_preimage_singleton 3
      (transcendental_xCoord_three_nsmul (W := W) h2 h3) q).toFinset
        = (finite_comapProjPointThree_preimage_singleton h2 h3 q).toFinset := by
    ext p
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff,
      comapProjPointN_three h2 h3 p]
  rw [hset]
  exact Finset.sum_congr rfl fun p _ => by
    rw [ramificationIdxN_three h2 h3 p, residueDegreeN_three h2 h3 p]

/-- **`∑_{p ↦ q} e_p · f_p = 9` for `[3]∗` in characteristic zero** — the `[3]`-indexed weighted
identity **without** `[IsAlgClosed F]`.

⚠️ `EllipticCurves.FunctionField.MulByThreeResidueDegree` **named** exactly this as what was
still absent, in what is its `## Scope` section (not a `## What is not here` — that file has no such
heading): *"what is still absent *here* is a `[3]` weighted identity without `[IsAlgClosed F]`"*.
It is the previous bridge composed with `sum_ramificationIdxN_mul_residueDegreeN_of_charZero` at
`n = 3`, and it is stated here rather than left as a two-step so that the bullet could be retired
against a name.  ⚠️ **It was — in the same commit (`4a30e82`) that added this file, which is why
the quotation above is historical from the moment it was written.**  That bullet now reads *"the
clause this bullet used to carry said it was absent, full stop, and that is now false of the
tree"*, and names this declaration.  Do not go looking for the quoted sentence.

The `n = 3` mirror of `sum_ramificationIdxTwo_mul_residueDegreeTwo_of_charZero`
(`EllipticCurves.FunctionField.PlaceInertiaGeneral`), which had none. -/
theorem sum_ramificationIdxThree_mul_residueDegreeThree_of_charZero [CharZero F] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointThree_preimage_singleton h2 h3 q).toFinset,
      (ramificationIdxThree h2 h3 p).toNat * residueDegreeThree h2 h3 p = 9 := by
  have hsmooth : ∀ p ∈ Nat.primeFactors 3, p = 2 ∨ p = 3 := by
    intro p hp
    exact Or.inr (Finset.mem_singleton.mp (Nat.prime_three.primeFactors ▸ hp))
  rw [← sum_ramificationIdxN_mul_residueDegreeN_three h2 h3 q]
  exact sum_ramificationIdxN_mul_residueDegreeN_of_charZero h2 h3 (by norm_num) hsmooth _ q

/-! ### Non-vacuity

Every statement above carries `[IsDedekindDomain W.CoordinateRing]` and `[W.IsElliptic]` on top of a
non-constancy hypothesis; `comapProjPointN`, `ramificationIdxN` and `residueDegreeN` are all
extracted from existence statements by choice, and `↥(placeBelowN W n h q)` carries five instances
found by search.  Curves on which the whole chain elaborates with nothing supplied by hand are
therefore committed rather than quoted.

⚠️ **Two curves are needed and neither will do alone.**  The `_of_smooth` statements want
`[IsAlgClosed F]`, which the `ℚ` curve of most of `FunctionField/` cannot supply; the `_of_charZero`
statements are interesting *only* over a field that is not algebraically closed, so a certificate
over `AlgebraicClosure ℚ` would certify the wrong thing.  `y² = x³ − x` over `ℚ` and `y² + y = x³`
over `AlgebraicClosure ℚ` are the two curves the merged layers already use, and they are used here
for the same reasons.

⚠️ The non-constancy hypothesis is **produced** at every index below, never assumed:
`transcendental_xCoord_nsmul_of_smooth` at `n = 12` and — this is what makes the `n = 5` certificate
possible — `transcendental_xCoord_nsmul_of_isAlgClosed`, which gives it at **every** `n ≠ 0` over an
algebraically closed base field. -/

section Nonvacuity

/-! The certificate curves `y² = x³ − x` and `y² + y = x³` are the shared
`EllipticCurves.Fixture.y2EqX3SubX` and `EllipticCurves.Fixture.y2AddYEqX3`, and the base —
algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here.  ⚠️ `y2EqX3SubX ℚ` is deliberately over `ℚ`, a base field that is **not**
algebraically closed — that is the point of the characteristic-zero statements; and
`y2AddYEqX3 AlgClosedQ` is the curve `#1219` certifies separability on, hence the one on which the
`_of_smooth` chain closes. -/

open EllipticCurves.Fixture

private lemma exampleQTwo : (2 : ℚ) ≠ 0 := by norm_num

private lemma exampleQThree : (3 : ℚ) ≠ 0 := by norm_num

/-- ⚠️ `decide` does **not** close this: `Nat.primeFactors` goes through `Nat.primeFactorsList`,
whose `Decidable` instance gets stuck on `Nat.minFac`'s well-founded recursion.  Bounding `p` and
case-splitting is what works — the same note `#1219` records. -/
private lemma smoothTwelve : ∀ p ∈ Nat.primeFactors 12, p = 2 ∨ p = 3 := by
  intro p hp
  obtain ⟨hp1, hp2, -⟩ := Nat.mem_primeFactors.mp hp
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) hp2
  interval_cases p <;> revert hp1 hp2 <;> decide

/-- **The identity at `n = 12` over `ℚ`, committed** — `∑_{p ↦ ∞} e_p · f_p = 144` on a genuine
curve over a base field that is not algebraically closed, where the collapsed form
`sum_ramificationIdxN_of_smooth` does not apply. -/
example : ∑ p ∈ (finite_comapProjPointN_preimage_singleton (W := y2EqX3SubX ℚ) 12
      (transcendental_xCoord_nsmul_of_smooth exampleQTwo exampleQThree (by norm_num) smoothTwelve)
      (none : ProjPoint (y2EqX3SubX ℚ))).toFinset,
      (ramificationIdxN 12 (transcendental_xCoord_nsmul_of_smooth exampleQTwo exampleQThree
          (by norm_num) smoothTwelve) p).toNat
        * residueDegreeN 12 (transcendental_xCoord_nsmul_of_smooth exampleQTwo exampleQThree
          (by norm_num) smoothTwelve) p = 144 :=
  sum_ramificationIdxN_mul_residueDegreeN_of_charZero exampleQTwo exampleQThree (by norm_num)
    smoothTwelve _ _

/-- **`f_∞ = 1` over `ℚ`**, at an index at which nothing merged says anything — and with no
`[IsAlgClosed F]`, which is what distinguishes this from *"every place is rational"*. -/
example : residueDegreeN (W := y2EqX3SubX ℚ) 12
    (transcendental_xCoord_nsmul_of_smooth exampleQTwo exampleQThree (by norm_num) smoothTwelve)
    (none : ProjPoint (y2EqX3SubX ℚ)) = 1 :=
  residueDegreeN_none_eq_one _ _

private lemma exampleBarTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleBarThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

/-- **The collapsed identity at `n = 12` over `F̄`, committed** — `∑_{p ↦ ∞} e_p = 144`, the
general-`n` shape of `sum_ramificationIdxTwo_eq_four` at an index at which neither merged
instantiation says anything. -/
example : ∑ p ∈ (finite_comapProjPointN_preimage_singleton (W := y2AddYEqX3 AlgClosedQ) 12
      (transcendental_xCoord_nsmul_of_smooth exampleBarTwo exampleBarThree (by norm_num)
        smoothTwelve) (none : ProjPoint (y2AddYEqX3 AlgClosedQ))).toFinset,
      (ramificationIdxN 12 (transcendental_xCoord_nsmul_of_smooth exampleBarTwo exampleBarThree
        (by norm_num) smoothTwelve) p).toNat = 144 :=
  sum_ramificationIdxN_of_smooth exampleBarTwo exampleBarThree (by norm_num) smoothTwelve _ _

/-- **The identity at `n = 5`, committed** — the index this tree reaches in no other statement about
`[n]∗`.

⚠️ The right-hand side is `[F(W) : [5]∗F(W)]` and is left as a `finrank` **here**, which is what
this certificate was originally for: when it was written, `#1213`'s degree was `3`-smooth and `5` is
not, so nothing evaluated it to `25`.  ⚠️ **That reason is now gone** — `sum_ramificationIdxN_five`
evaluates it, and the certificate immediately below commits the evaluated form on this same curve.
This one is kept because it commits the *identity* form
(`sum_ramificationIdxN_mul_residueDegreeN_finrank_of_charZero`, which carries no hypothesis on `n`
at all) rather than the value, so the two are certified through genuinely different lemmas and a
regression in either is visible on its own.  ⚠️ **This is the right witness for the module
docstring's *"the identity is wider than the value"* distinction, and `n = char F` is not** — the
identity lemma needs `hsep`, and `hsep` is exactly what fails at `n = char F`, so it is vacuous
there rather than wider.  The non-constancy of `[5]` comes from
`transcendental_xCoord_nsmul_of_isAlgClosed`, which is the only route to it at a non-`3`-smooth
index in this tree. -/
example : ∑ p ∈ (finite_comapProjPointN_preimage_singleton (W := y2AddYEqX3 AlgClosedQ) 5
      (transcendental_xCoord_nsmul_of_isAlgClosed exampleBarTwo (by norm_num))
      (none : ProjPoint (y2AddYEqX3 AlgClosedQ))).toFinset,
        (ramificationIdxN 5
          (transcendental_xCoord_nsmul_of_isAlgClosed exampleBarTwo (by norm_num)) p).toNat
          * residueDegreeN 5
            (transcendental_xCoord_nsmul_of_isAlgClosed exampleBarTwo (by norm_num)) p
      = finrank ↥(mulByNEndo (W := y2AddYEqX3 AlgClosedQ) 5
          (transcendental_xCoord_nsmul_of_isAlgClosed exampleBarTwo (by norm_num))).fieldRange
        (y2AddYEqX3 AlgClosedQ).FunctionField :=
  sum_ramificationIdxN_mul_residueDegreeN_finrank_of_charZero _ _ _

private lemma exampleBarFive : ((5 : ℕ) : AlgClosedQ) ≠ 0 := by
  have : ((5 : ℕ) : AlgClosedQ) = 5 := by push_cast; ring
  rw [this]; norm_num

private lemma exampleBarFourteen : ((14 : ℕ) : AlgClosedQ) ≠ 0 := by
  have : ((14 : ℕ) : AlgClosedQ) = 14 := by push_cast; ring
  rw [this]; norm_num

/-- **The identity at `n = 5` with the right-hand side EVALUATED, committed** — `∑_{p ↦ ∞} e_p = 25`
on the same curve as the `finrank` certificate above.

⚠️ This is the one certificate that the `3`-smooth chain provably could not produce, and the reason
is arithmetic rather than effort: `5 ∤ 2^a · 3^b` for any `a, b`, so
`Nat.exists_eq_two_pow_mul_three_pow` — the first step of every `_of_smooth` proof in this file —
cannot even be applied. -/
example : ∑ p ∈ (finite_comapProjPointN_preimage_singleton (W := y2AddYEqX3 AlgClosedQ) 5
      (transcendental_xCoord_nsmul_of_isAlgClosed exampleBarTwo (by norm_num))
      (none : ProjPoint (y2AddYEqX3 AlgClosedQ))).toFinset,
      (ramificationIdxN 5
        (transcendental_xCoord_nsmul_of_isAlgClosed exampleBarTwo (by norm_num)) p).toNat
      = 5 ^ 2 :=
  sum_ramificationIdxN_of_ne_zero exampleBarTwo exampleBarFive _ _

/-- **⚠️ THE LOAD-BEARING CERTIFICATE: `n = 14`.**  `∑_{p ↦ ∞} e_p · f_p = 196`, at an index that is
**even and not `3`-smooth**.

`n = 5` alone cannot show the statements above are general rather than `{2, 3, 5}`-parametrised, and
it cannot show they are not an odd-`n` package in disguise.  `14 = 2 · 7` is reachable by **no**
`3`-smooth statement (`7 ∤ {2, 3}`) and by **no** odd-`n` statement, so this certificate can come
only from `sum_ramificationIdxN_mul_residueDegreeN_of_ne_zero` by name.  ⚠️ The same index is what
`#1523`'s review of PR #593 used on the Galois half, for the same reason. -/
example : ∑ p ∈ (finite_comapProjPointN_preimage_singleton (W := y2AddYEqX3 AlgClosedQ) 14
      (transcendental_xCoord_nsmul_of_isAlgClosed exampleBarTwo (by norm_num))
      (none : ProjPoint (y2AddYEqX3 AlgClosedQ))).toFinset,
      (ramificationIdxN 14
        (transcendental_xCoord_nsmul_of_isAlgClosed exampleBarTwo (by norm_num)) p).toNat
        * residueDegreeN 14
          (transcendental_xCoord_nsmul_of_isAlgClosed exampleBarTwo (by norm_num)) p
      = 14 ^ 2 :=
  sum_ramificationIdxN_mul_residueDegreeN_of_ne_zero exampleBarTwo exampleBarFourteen _ _

/-- **The degree at `n = 14`, committed** — `[F(W) : [14]∗F(W)] = 196`, the input the certificate
above consumes, exhibited separately so that a reader can see the value is not assumed. -/
example : finrank ↥(mulByNEndo (W := y2AddYEqX3 AlgClosedQ) 14
      (transcendental_xCoord_nsmul_of_isAlgClosed exampleBarTwo (by norm_num))).fieldRange
    (y2AddYEqX3 AlgClosedQ).FunctionField = 14 ^ 2 :=
  finrank_mulByNEndoFieldRange_of_ne_zero exampleBarTwo exampleBarFourteen _

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
