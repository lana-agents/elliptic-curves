/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.MulByNInertia
import EllipticCurves.FunctionField.MulByNYCoordFormula
import EllipticCurves.FunctionField.MulByThreeFibre
import EllipticCurves.Torsion.NsmulSmoothSurjective

/-!
# The place contraction of `[n]∗` **is** `[n]` on rational points, and the fibre over one

`EllipticCurves.FunctionField.MulByTwoFibreAffine` (`#774`) proves

```
comapProjPointTwo h2 (projPointOfPoint P) = projPointOfPoint (2 • P)
```

for every `P : W.Point`, and `EllipticCurves.FunctionField.MulByThreeFibre` proves its `n = 3`
mirror.  From each, over `F̄`, that file computes the fibre — a coset of `E[2]` (resp. `E[3]`), of
size `4` (resp. `9`), every ramification index `1`, and the divisor identity `[n]∗(S) = ∑_{p ↦ S}
(p)` that `#418`'s `hprin` consumes.  **Neither had a general-`n` form, and this file supplies two
independent ones** — the composition ladder at every `3`-smooth `n`, and the coordinate formulas at
every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` (`#1540` items 2 and 3).  ⚠️ This paragraph
used to end *"and this file supplies one at every `3`-smooth `n`"*; neither layer subsumes the
other's *proof*, and the second subsumes the first's *statements*, which the `example`s below
compile.

⚠️ **The title used to carry the two ranges, and it never rendered them** (`#1667`).  It read
*"The place contraction of `[n]∗` **is** `[n]` on rational points, and the fibre over one — at every
`3`-smooth `n` by composition, and at every `n` with `((n : ℤ) : F) ≠ 0` by the coordinate
formulas"* from `135f257` (`#1540`, PR #612) onwards, written across three source lines — and a
Markdown heading ends at the end of its own line, so the H1 doc-gen printed was
*"…and the fibre over one — at"*, with the rest below it as an ordinary paragraph.  ⚠️ **It could
not be repaired in place, because the corrected clause does not fit on one line**: every
general-`n` statement in this file binds `(2 : F) ≠ 0` as well — the `_of_smooth` family takes it
with `(3 : F) ≠ 0`, the `_of_ne_zero` family with `((n : ℤ) : F) ≠ 0` — and naming all three
conditions costs more than the hundred columns a heading has.  So the title now names **none** of
them, which is `README.md` `### Reach clauses`' second branch, and the paragraph above states both
ranges with `(2 : F) ≠ 0` in place.

## Why composition reaches this, and what it costs

`[m · n]∗ = [m]∗ ∘ [n]∗` (`mulByNEndo_mul`, `#1213`) contracts places covariantly
(`comapProjPointN_mul`, `EllipticCurves.FunctionField.MulByNPlaceComposition`), so an index
`2 ^ a · 3 ^ b` is reached by peeling one prime at a time off the two merged computations.  ⚠️ **No
coordinate formula is evaluated at any new index.**  `addY_self_eq_div`
(`EllipticCurves.Torsion.DoublingCoords`) and its `n = 3` mirror
(`EllipticCurves.Torsion.TriplingCoords`) enter exactly where they already did, at `n = 2` and
`n = 3`, and the general-`n` `ωₙ` duplication formula is not approached.  ⚠️ That formula used to
be named here as `#251`, **not** `#404`; the attribution was right and the openness is not — it
holds at every index with `(2 : F) ≠ 0` (`nsmul_eq_some_omegaY_of_ΨSq_ne_zero`,
`EllipticCurves.Torsion.NsmulYPeriodic`, `#1500`, PR #579).  ⚠️ **This paragraph used to end
*"Nothing below consumes it."*  That was true of the `3`-smooth layer and is false of the file**:
`ord_mulByNCoordHom_YClass_pos` consumes exactly that formula, and it is the step that closes the
affine non-torsion branch of `#1540` item 2.  The sentence about the `3`-smooth layer stands: no
coordinate formula is evaluated at any new index *by the composition ladder*.

## ⚠️ The induction here is *not* the one `#1214` ran, and the difference is the whole difficulty

`comapProjPointN_two_pow_mul_three_pow_none` (`EllipticCurves.FunctionField.MulByNPlaceComposition`)
runs the same double induction at the point at infinity.  **There the point is a fixed point** —
`comapProjPointTwo none = none` — so the induction hypothesis is a statement about one place and
needs no generalisation.  **Here the point moves**: peeling `[2]` off `[2 ^ (a+1) · 3 ^ b]` leaves
`[2 ^ a · 3 ^ b]` applied to `projPointOfPoint (2 • P)`, a *different* rational point.  The
induction must therefore be generalised over `P`, and what makes that legitimate is that
`projPointOfPoint (2 • P)` is again in the rational locus — the class the merged statements are
about is closed under the map.  ⚠️ A reader who reads this file as *"`#1214` with `none` replaced by
`projPointOfPoint P`"* has the shape right and the reason wrong.

## Main statements

⚠️ Every public declaration of this file is listed.

* `…comapProjPointN_two_pow_mul_three_pow_projPointOfPoint` — the double induction, at an index
  presented as `2 ^ a * 3 ^ b`;
* **`…comapProjPointN_projPointOfPoint_of_smooth`** — the headline, `comapProjPointN n h
  (projPointOfPoint P) = projPointOfPoint (n • P)` with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, at every
  `3`-smooth `n ≠ 0`;
* `…projPointOfPoint_add_injective` — `R ↦ P ⊕ R` is injective into the places, at **every** `n`
  and with no hypothesis on `F`.  ⚠️ The merged `…_two` and `…_three` forms of this carry an index
  that their proof never uses;
* `…comapProjPointN_add_torsion_of_smooth` — the coset `{ P ⊕ R : R ∈ E[n] }` lies in the fibre;
* over `F̄`: `…card_fibre_comapProjPointN_le_sq`, **`…card_fibre_comapProjPointN_projPointOfPoint`**
  (`= n ^ 2`), `…fibre_comapProjPointN_eq_range` (the fibre **is** that coset),
  `…ramificationIdxN_eq_one_of_comapProjPointN_eq_projPointOfPoint`,
  `…pullbackDivisorN_single_projPointOfPoint` (`[n]∗(S) = ∑_{p ↦ S} (p)`) and
  `…pullbackDivisorN_single_eq_sum_torsion` (`[n]∗(S) = ∑_{R ∈ E[n]} (P ⊕ R)`).
* ⚠️ `card_fibre_comapProjPointN_le_sq_of_ne_zero` and `card_fibre_comapProjPointN_le_sq_five` —
  the fibre bound `≤ n²` over `F̄`, with `(2 : F) ≠ 0`, at every `n` with `(n : F) ≠ 0` (`#1523`
  item 4).  ⚠️ The second is the first at `n = 5`, so the index condition it binds is
  `(5 : F) ≠ 0`; it is that clause at that index and not a further hypothesis.  ⚠️ **This
  bullet used to call it *"the only statement in this file that lifts"*.**  It was, and it is not:
  it is the only one that lifted *off the fundamental identity alone*, and the seven below lift
  off the coordinate formulas.

### The general layer — `#1540` item 2 and its six consumers

⚠️ **No `_of_smooth` statement is deleted**: each is restated verbatim as an `example` and proved
from its general companion, so the containment is compiled rather than claimed.

* `…mulByNEndo_algebraMap`, `…mulByNCoordHom_injective`, `…mulByNCoordHom_XClass`,
  `…mulByNCoordHom_YClass` — the general-`n` forms of the `mulByTwoCoordHom` basics.  ⚠️ These four
  take **neither** `(2 : F) ≠ 0` **nor** `((n : ℤ) : F) ≠ 0`: they hold at every `n`, on the
  transcendence hypothesis alone.  ⚠️ **Every one of the thirteen below does take both.**
  ⚠️ **Where a bullet says nothing about hypotheses, read it against this register; where a bullet
  counts them, the count is that bullet's own claim and no register makes it true.**  Naming some
  without counting is neither, and sits under this register unchanged; reporting one *discharged* is
  a gate-discharge claim, which `README.md` `### Gate-discharge claims` governs;
* `…ord_mulByNCoordHom_XClass_pos` and `…ord_mulByNCoordHom_YClass_pos` — `x ∘ [n] − x(n • P)` and
  `y ∘ [n] − y(n • P)` vanish at an affine `P` that is not `n`-torsion.  ⚠️ The second is the step
  neither `#774` nor `#1540` priced, and it is the one that needs `ωₙ`;
* `…ord_mulByNEndo_genX_nonneg` and `…ord_mulByNEndo_genX_neg` — `x ∘ [n]` is regular off the
  `n`-torsion locus and has a pole on it;
* `…comapProjPointN_pointClosedPoint_of_ΨSq_ne_zero` and
  `…comapProjPointN_pointClosedPoint_of_eval_ΨSq_eq_zero` — the two affine branches;
* **`…comapProjPointN_projPointOfPoint_of_ne_zero`** — `#1540` item 2, the three branches
  assembled;
* `…comapProjPointN_add_torsion_of_ne_zero`, and over `F̄`
  **`…card_fibre_comapProjPointN_projPointOfPoint_of_ne_zero`**,
  `…fibre_comapProjPointN_eq_range_of_ne_zero`,
  `…ramificationIdxN_eq_one_of_comapProjPointN_eq_projPointOfPoint_of_ne_zero`,
  `…pullbackDivisorN_single_projPointOfPoint_of_ne_zero` and
  `…pullbackDivisorN_single_eq_sum_torsion_of_ne_zero` — `#1540` item 3, the six consumers, whose
  proofs are their `3`-smooth originals with `hfac` deleted.

⚠️ **The register heading this sub-list formerly closed *"and the bullets give the conclusions and
not the hypotheses"***, and it was false of the thirteen it is scoped to **on the day it landed** —
the register and the rows that falsify it are one commit, `135f257` (`#1540` items 2 and 3,
PR #612).  The `ord_mulByNCoordHom_XClass_pos` / `…_YClass_pos` row names *"vanish at an affine `P`
that is not `n`-torsion"* over `(h : W.Equation x y)` and `(hΨ : (W.ΨSq n).eval x ≠ 0)`, and the
`ord_mulByNEndo_genX_nonneg` / `…_neg` row *"regular off the `n`-torsion locus and has a pole on
it"* over that same pair, `(hx : (W.ΨSq n).eval x = 0)` on the pole side — explicit binders of the
declarations those rows are about, named in the same shape as
`WeilPairingAlternatingConsumerN`'s *"at every `3`-smooth `n ≠ 0`"* (`#1686`).  ⚠️ **A bullet that
NAMES a hypothesis falsifies that sentence**; **counting** them is the narrower, stronger failure
the form above routes separately.  What replaces it is that form, in the register's own bullet.

⚠️ **This answers whether the register's universal was TRUE, and not whether any row is
COMPLIANT** — two questions in opposite directions, and `README.md` `### Module-block bullets`
already rules on the second for the sixth row of this list, *"a reach clause naming the instance and
nothing else … so the bullet is compliant relative to it"*.  ⚠️ **That ruling is untouched here and
no row is edited**: it says a bullet naming less than its signature binds is cleared by the register
above it, where the retired sentence claimed the bullets name **nothing**, which is a claim about
the bullets and not about their signatures.  ⚠️ **The verdict does not turn on the sixth row's
*"over `F̄`"*** either — that phrase names an **instance**, `README.md` rules in terms that *"the
reach-clause rule never reached instances"*, and the two rows above settle the universal without it.
So nothing here reopens the instance question (`#1686`).

## What is *not* here

* ⚠️ **`n = char F`, and nothing else on the index axis.**  ⚠️ **This bullet used to say `n = 5`
  was reached *"for the BOUND only"*, and to state a gate that no longer exists**: *"the real gate
  is `comapProjPointN_two_pow_mul_three_pow_projPointOfPoint` (`:157`), a composition ladder …
  a general-`n` proof needs the three-way case split of `comapProjPointTwo_projPointOfPoint` …
  run against `Φₙ/ΨSqₙ` at the level of places.  That is new mathematics, it is `#1540` item 2."*
  That diagnosis was exact and the work is done: every statement in this file now has an
  `_of_ne_zero` companion, `n = 5` included, and the section below records what the measurement got
  right and the two inputs it did not name.
  ⚠️ **What remains excluded is an `n` divisible by the characteristic**, and the reason differs
  by declaration — ⚠️ **it is one reason for five of the seven and a different one for the other
  two, and saying it once for all seven overstates what is known.**
  For the ramification and fibre statements it is excluded because they are **false** there: at
  `n = char F > 2` the ramification index at infinity alone is `n` or `n²` rather than `1`
  (`ramificationIdxN_none_of_ne_zero`, `EllipticCurves.FunctionField.MulByNPlaceComposition`), and
  `O` is a rational point, so `ramificationIdxN_eq_one_…_of_ne_zero` fails; `#E[p] ≤ p < p²` kills
  the fibre count with it.  No better proof removes `((n : ℤ) : F) ≠ 0` from those.
  ⚠️ **For the contraction and `comapProjPointN_add_torsion_of_ne_zero` that argument does not
  apply**, and nothing in this tree says either is false at `n = char F`: see the sharpness
  paragraph on `comapProjPointN_projPointOfPoint_of_ne_zero` below.
  ⚠️ For the record, since four revisions of this bullet blamed them: **none** of the coordinate
  formula (`hasXCoordFormula_of_two_ne_zero`, `EllipticCurves.Torsion.NsmulOrder`),
  `[n]`-surjectivity on `E(F̄)` (`nsmul_surjective_of_two_ne_zero`,
  `EllipticCurves.Torsion.TwoTorsionOrder`), the transcendence input
  (`transcendental_xCoord_nsmul_of_isAlgClosed`,
  `EllipticCurves.FunctionField.MulByNTranscendence`) or the count `card_torsion_eq_sq`
  (`EllipticCurves.Torsion.StructureGeneral`, `#293`, at every `n` with `(2 : F) ≠ 0` and
  `(n : F) ≠ 0`) was ever the gate; the first and last are *consumed* by the general layer, in the
  same places their `3`-smooth twins are consumed by the `3`-smooth one.
* **No statement at a place that is not the place of a rational point.**  As `#774` records of its
  own `n = 2` case, this is *not* "`[n]` is unramified": a place lying over a closed point which is
  not the closed point of an `F`-rational point is untouched, and this tree has no proof that there
  are none.  Over `F̄` the two coincide, and every `[IsAlgClosed F]` statement here should be read
  that way.
* **No `hprin`.**  `…pullbackDivisorN_single_eq_sum_torsion` is the *fibre description*, which is
  one input to the rung-4 divisor identity; `exists_gS_n` is
  `EllipticCurves.FunctionField.NthRootOfPullbackN` and nothing in this file discharges it.
* **No new `E[n]` structure.**  `#E[n] = n²` is `card_torsion_eq_sq_of_smooth`
  (`EllipticCurves.Torsion.ThreePrimary`) at `3`-smooth `n` and `card_torsion_eq_sq`
  (`EllipticCurves.Torsion.StructureGeneral`, `#293`) at every `n` with `(2 : F) ≠ 0` and
  `(n : F) ≠ 0`; both are merged, both are consumed rather than reproved, and neither is a gate on
  anything here.  ⚠️ **`(2 : F) ≠ 0` is the second hypothesis of the general count and this bullet
  used to name only the index one** (`#1137`); it is why that count reaches no curve in
  characteristic `2`, at any index.  ⚠️ **The
  correction this bullet used to carry — that the bullet above was stale where it called the count
  *"still `3`-smooth"* — has been folded into that bullet**, so the pair of a correction pointing
  back at an uncorrected sentence is gone; PR #593's review asked for exactly that.

⚠️ **That pair is paid on both halves, and `(n : F) ≠ 0` is what is left.**  PR #557 proved the
on-curve identity for `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` at every index over a field with `(2 : F) ≠ 0` and under
`ψₙ(x, y) ≠ 0` (`WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero`,
`EllipticCurves.Torsion.OmegaCrux`) — that was `#404`, and it says only that those coordinates lie
on the curve.  Identifying the `x`-coordinate with the group-law multiple `n • P` is `#251`, and it
is **closed**: `WeierstrassCurve.Affine.hasXCoordFormula_of_two_ne_zero`
(`EllipticCurves.Torsion.NsmulOrder`) at every index over any field with `(2 : F) ≠ 0`, and in
function-field form `nMulRatFunc_eq_ΦDivΨSq` (`EllipticCurves.FunctionField.MulByNXCoordFormula`) at
every `n` with `((n : ℤ) : F) ≠ 0`.  ⚠️ **`#1184` has since been discharged over a field** —
`WeierstrassCurve.Affine.isCoprime_ΨSq_adjacent` (`EllipticCurves.Torsion.CoprimeAdjacent`) at every
`n : ℤ` for an elliptic curve of characteristic `≠ 2` — so `[F(W) : [n]∗F(W)] = n²` at general `n`
(`EllipticCurves.FunctionField.MulByNDegreeGeneral`) is owed `((n : ℤ) : F) ≠ 0` and nothing else
beyond the `(2 : F) ≠ 0` and `[W.IsElliptic]` that this whole paragraph already carries.  ⚠️ The
arbitrary-**ring** form that `EllipticCurves.DivisionPolynomial.Coprime` states is still open.  ⚠️
And the `y`-half — `ωₙ/(2ψₙ³)` as `y(n • P)` — **is closed too, at every index**:
`nsmul_eq_some_omegaY_of_ΨSq_ne_zero` (`EllipticCurves.Torsion.NsmulYPeriodic`, PR #579), under the
same `ΨSqₙ(x) ≠ 0` and `(2 : F) ≠ 0` the `x`-half asks.  ⚠️ So the whole *pair* is available at
every index, and the `#251` bullets on the Weil-pairing front no longer name an open gate.  ⚠️
**This paragraph used to end *"None of `EllipticCurves.Torsion.NsmulOrder`,
`EllipticCurves.FunctionField.MulByNXCoordFormula`, `EllipticCurves.Torsion.CoprimeAdjacent` or
`EllipticCurves.FunctionField.MulByNDegreeGeneral` is in this file's import closure and none is
added: all four names are cited, not consumed."*  All four were in it when that was written**, and
by the same edge — this file imports `EllipticCurves.FunctionField.MulByNInertia`, which imports
`…MulByNDegreeGeneral`, which imports `…MulByNXCoordFormula` and
`EllipticCurves.Torsion. CoprimeAdjacent`, and `…MulByNXCoordFormula` imports
`EllipticCurves.Torsion.NsmulOrder`.  Two of the four are now **consumed** rather than cited:
`isCoprime_Φ_ΨSq` closes the affine `n`-torsion branch, and
`transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero` produces the non-constancy input of
the `n = 14` certificates.  ⚠️ The **one** module this file gained is
`EllipticCurves.FunctionField.MulByNYCoordFormula`, for the `ωₙ` half (`155 → 156`).  The
two-reading account is `EllipticCurves.FunctionField.MulByNPullback`.

## The non-constancy hypothesis is not named in the headlines below

Where a statement here takes `h : Transcendental F (n • genericPoint).xCoord` as an explicit
argument, its **headline** does not name it, under `README.md`'s derivability exemption: at a
`3`-smooth `n ≠ 0` with `(2 : F) ≠ 0` and `(3 : F) ≠ 0` it is
`transcendental_xCoord_nsmul_of_smooth` (`EllipticCurves.FunctionField.MulByNComposition`), and at
a general `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` it is
`transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`
(`EllipticCurves.FunctionField.MulByNXCoordFormula`).  Each derives `h` from exactly what the
clause above it names.

⚠️ **That sentence used to quantify over every reach clause, and this file's own module block
falsifies the wider form** (`#1696`).  Until now it read *"no reach clause names it"*, and two
clauses here name it:

* `### The general layer`'s first bullet, of `…mulByNEndo_algebraMap`,
  `…mulByNCoordHom_injective` and their two siblings — *"they hold at every `n`, on the
  transcendence hypothesis alone"*.  ⚠️ **A reach phrase and the parameter in one clause**, which
  is the shape `README.md` `### Reach clauses` defines and the strongest falsifier this sentence
  has;
* `### Non-vacuity`'s opening — *"Every statement in this file carries
  `[IsDedekindDomain W.CoordinateRing]` and `[W.IsElliptic]` **on top of a non-constancy
  hypothesis**"* — the hypothesis-load shape `EllipticCurves.FunctionField.MulByNInertia` counts
  among its own nine (`#1669`, PR #671).

⚠️ **The heading's claim is the narrower one and it stands.**  Neither falsifier is a headline: the
first is a module-block bullet and the second a section gloss, and **no** declaration headline here
that takes `h` names the parameter.  The one headline that names it —
`exampleFibreFourteenT`'s *"The non-constancy input at `n = 14`, **produced** from the index
condition alone"* — is a statement whose *conclusion* is the non-constancy and which takes no `h`
at all, which is the case the paragraph below already carves out in terms.  ⚠️ **Recorded so the
next census does not re-open it**: a census keyed on the words rather than on the role convicts
that row, and it should not.

Recogniser, published beside the count as `README.md` `### Module-block bullets` asks: every prose
occurrence of *"non-constan…"* or *"transcenden…"* at or below the `## Main statements` heading,
outside backticks, inside a comment, and **outside this section** — ⚠️ this section is where the
repair went, so a recogniser that included it would count its own repair — read one by one.
**Six** occur, and only the two above are clauses:

* `exampleFibreFourteenT`'s headline, the *produces*-rather-than-takes row ruled on above;
* the gate-attribution bullet's *"the transcendence input"*, which cites
  `transcendental_xCoord_nsmul_of_isAlgClosed` to say it was never the gate — a citation, and
  backticked names are excluded anyway (PR #671's exclusion);
* the import census's note that the same lemma *"produces the non-constancy input of the `n = 14`
  certificates"*, which is about this file's imports;
* `### Non-vacuity`'s *"The non-constancy hypothesis is **produced**, never assumed"*, which
  quantifies over one certificate rather than over the declarations below.  ⚠️ The reach phrase its
  `EllipticCurves.FunctionField.MulByNInertia` twin carries — *"produced **at every index below**,
  never assumed"* — is exactly what this one lacks, and that phrase is why the twin counts and this
  does not.

⚠️ **The wider wording was false on the day it landed**, not stale by growth.  `1ed28ec` (`#1574`,
PR #625) wrote it and the `### The general layer` bullet in one commit — `git show 1ed28ec:…` lines
`93` and `196`.  False rather than partial, so `README.md` `### Retired claims` binds and the
wording is quoted here rather than deleted.  What replaced it is the headline-scoped claim above,
which is what the heading has said all along.

⚠️ **Two statements below take no such argument, and this paragraph is not about them.**
`projPointOfPoint_add_injective` holds at every `n` with no hypothesis on `F` at all, as its own
docstring says; `card_fibre_comapProjPointN_le_sq_five` *produces* the transcendence at `n = 5`
from `(2 : F) ≠ 0` and `(5 : F) ≠ 0` rather than taking it, so those two are what its headline has
to name and it names them.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.10 and III.6.4 —
  `[n]` is surjective with kernel of order `n²` over an algebraically closed field, which is the
  statement `card_fibre_comapProjPointN_projPointOfPoint` is the function-field shadow of.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}
  [IsDedekindDomain W.CoordinateRing] [W.IsElliptic]

/-! ### The contraction at a rational point -/

/-- **`[2 ^ a · 3 ^ b]∗` contracts the place of `P` to the place of `(2 ^ a · 3 ^ b) • P`**, at
every `2 ^ a · 3 ^ b` with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`.

Induction on `a` and then on `b`, **generalising over `P`** at both levels: each step peels one
prime off the index with `comapProjPointN_of_mul_eq` and lands the merged
`comapProjPointTwo_projPointOfPoint` / `comapProjPointThree_projPointOfPoint`, whose output is the
place of a *different* rational point.  See the module docstring on why that is the only difference
from `comapProjPointN_two_pow_mul_three_pow_none` and why it is the load-bearing one. -/
theorem comapProjPointN_two_pow_mul_three_pow_projPointOfPoint (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (a b : ℕ) (h : Transcendental F ((2 ^ a * 3 ^ b) • genericPoint (W := W)).xCoord)
    (P : W.Point) :
    comapProjPointN (2 ^ a * 3 ^ b) h (projPointOfPoint W P)
      = projPointOfPoint W ((2 ^ a * 3 ^ b) • P) := by
  induction a generalizing P with
  | zero =>
    induction b generalizing P with
    | zero => simpa using comapProjPointN_one h (projPointOfPoint W P)
    | succ b ih =>
      have hb := transcendental_xCoord_two_pow_mul_three_pow_nsmul (W := W) h2 h3 0 b
      rw [comapProjPointN_of_mul_eq (m := 3) (n := 2 ^ 0 * 3 ^ b) (by ring)
        (transcendental_xCoord_three_nsmul h2 h3) hb h, comapProjPointN_three h2 h3,
        comapProjPointThree_projPointOfPoint h2 h3, ih hb, smul_smul]
      ring_nf
  | succ a ih =>
    have ha := transcendental_xCoord_two_pow_mul_three_pow_nsmul (W := W) h2 h3 a b
    rw [comapProjPointN_of_mul_eq (m := 2) (n := 2 ^ a * 3 ^ b) (by ring)
      (transcendental_xCoord_two_nsmul h2) ha h, comapProjPointN_two h2,
      comapProjPointTwo_projPointOfPoint h2, ih ha, smul_smul]
    ring_nf

/-- **The place contraction of `[n]∗` on the rational locus is the group-theoretic `n •`**, at
every `3`-smooth `n ≠ 0` with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`:

```
comapProjPointN n h (projPointOfPoint P) = projPointOfPoint (n • P).
```

The general-`n` form of `#774`'s `comapProjPointTwo_projPointOfPoint` and of
`comapProjPointThree_projPointOfPoint`, and the affine companion of `#1214`'s
`comapProjPointN_none_of_smooth`.  No case hypothesis on `P` and no torsion side condition.

⚠️ **The companion at infinity has since outgrown this one, and the asymmetry is the whole of
`#1540`.**  `comapProjPointN_none_of_ne_zero`
(`EllipticCurves.FunctionField.MulByNPlaceComposition`, PR #599) states the `P = O` case at every
`n` with `((n : ℤ) : F) ≠ 0`, off the pole order.  There is no such route here: at an affine
rational point `genX` has no pole and hence no sign to exploit, so this statement is still the
composition ladder and still `3`-smooth. -/
theorem comapProjPointN_projPointOfPoint_of_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (P : W.Point) :
    comapProjPointN n h (projPointOfPoint W P) = projPointOfPoint W (n • P) := by
  obtain ⟨a, b, rfl⟩ := Nat.exists_eq_two_pow_mul_three_pow n hn hfac
  exact comapProjPointN_two_pow_mul_three_pow_projPointOfPoint h2 h3 a b h P

omit [W.IsElliptic] in
/-- **`R ↦ P ⊕ R` is injective into the places**, for `R` ranging over `E[n]`: the group law is
cancellative and `projPointOfPoint` is injective.

⚠️ Stated at every `n`, with no hypothesis on `F` and none on the curve beyond what `W.Point`
needs.  The merged `projPointOfPoint_add_injective_two` and `…_three` are this statement with an
index their one-line proofs never use. -/
theorem projPointOfPoint_add_injective (n : ℕ) (P : W.Point) :
    Function.Injective fun R : W.torsion n => projPointOfPoint W (P + R) :=
  fun _ _ hEq => Subtype.ext (add_right_injective P (projPointOfPoint_injective hEq))

/-- **`P ⊕ R` lies over `n • P`, for every `R ∈ E[n]`**, at every `3`-smooth `n ≠ 0` with
`(2 : F) ≠ 0` and `(3 : F) ≠ 0`: the coset of `E[n]` through any `P` with `n • P = S` sits inside
the fibre over `S`.  This is the inclusion `⊇` of the fibre description; the reverse is pure
counting and needs `[IsAlgClosed F]`. -/
theorem comapProjPointN_add_torsion_of_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) {S P : W.Point} (hP : n • P = S)
    (R : W.torsion n) :
    comapProjPointN n h (projPointOfPoint W (P + R)) = projPointOfPoint W S := by
  rw [comapProjPointN_projPointOfPoint_of_smooth h2 h3 hn hfac h, smul_add, hP,
    mem_torsion_iff.mp R.2, add_zero]

/-! ### The contraction at a rational point, at every `n` with `((n : ℤ) : F) ≠ 0`

⚠️ **This is the case analysis the section below predicted and priced** — the `n = 2` three-way
split of `comapProjPointTwo_projPointOfPoint`
(`EllipticCurves.FunctionField.MulByTwoFibreAffine`) run against `Φₙ/ΨSqₙ` at the level of places
rather than of points, exactly as `#1540` item 2 asked for.  It touches the composition ladder
`comapProjPointN_two_pow_mul_three_pow_projPointOfPoint` nowhere, and the `_of_smooth` layer above
is kept for the standing reason: its proof composes `[2]∗` and `[3]∗` and evaluates no division
polynomial, so it is an independent route to the same conclusion on the common range.

The three branches, and where each one's work is:

* **`P = O`** — `comapProjPointN_none_of_ne_zero` (`#1540` item 1, PR #599), off the pole order.
* **`P` affine with `ΨSqₙ(x(P)) ≠ 0`**, i.e. `n • P ≠ O` — the crux.  `x ∘ [n] − x(n • P)` and
  `y ∘ [n] − y(n • P)` both vanish at `P`, so the two generators of the closed point of `n • P` lie
  in the contracted prime, which is maximal and therefore equal to it.
* **`P` affine with `ΨSqₙ(x(P)) = 0`**, i.e. `n • P = O` — `x ∘ [n]` has a **pole** at `P`, because
  `Φₙ` and `ΨSqₙ` are coprime (`isCoprime_Φ_ΨSq`, `EllipticCurves.Torsion.CoprimeAdjacent`), so the
  contracted place cannot be affine.
-/

omit [DecidableEq F] [IsDedekindDomain W.CoordinateRing] in
/-- `[n]∗` restricted along the structural embedding `F[W] →+* F(W)` is `mulByNCoordHom`. -/
@[simp] lemma mulByNEndo_algebraMap (n : ℕ)
    (hT : Transcendental F (n • genericPoint (W := W)).xCoord) (a : W.CoordinateRing) :
    mulByNEndo n hT (algebraMap W.CoordinateRing W.FunctionField a) = mulByNCoordHom n hT a :=
  pointEndo_algebraMap _ _ a

omit [DecidableEq F] [IsDedekindDomain W.CoordinateRing] in
/-- **Dominance for `mulByNCoordHom`** — the general-`n` form of `mulByTwoCoordHom_injective`. -/
theorem mulByNCoordHom_injective (n : ℕ)
    (hT : Transcendental F (n • genericPoint (W := W)).xCoord) :
    Function.Injective (mulByNCoordHom n hT) :=
  pointCoordHom_injective _ hT

omit [DecidableEq F] [IsDedekindDomain W.CoordinateRing] in
/-- `[n]∗(X - x₂) = x ∘ [n] - x₂`.  The general-`n` form of `mulByTwoCoordHom_XClass`. -/
theorem mulByNCoordHom_XClass (n : ℕ)
    (hT : Transcendental F (n • genericPoint (W := W)).xCoord) (x₂ : F) :
    mulByNCoordHom n hT (XClass W x₂)
      = mulByNEndo n hT (genX W) - algebraMap F W.FunctionField x₂ := by
  rw [← mulByNEndo_algebraMap n hT, ← genPsi, XClass, C_sub, map_sub, map_sub,
    genPsi_mk_CC, ← genX, map_sub, mulByNEndo_algebraMap_base]

omit [DecidableEq F] [IsDedekindDomain W.CoordinateRing] in
/-- `[n]∗(Y - y₂) = y ∘ [n] - y₂`.  The general-`n` form of `mulByTwoCoordHom_YClass`. -/
theorem mulByNCoordHom_YClass (n : ℕ)
    (hT : Transcendental F (n • genericPoint (W := W)).xCoord) (y₂ : F) :
    mulByNCoordHom n hT (YClass W (C y₂))
      = mulByNEndo n hT (genY W) - algebraMap F W.FunctionField y₂ := by
  rw [← mulByNEndo_algebraMap n hT, ← genPsi, YClass, map_sub, map_sub, genPsi_mk_CC,
    show mk W Y = AdjoinRoot.root W.polynomial from rfl, ← genY, map_sub,
    mulByNEndo_algebraMap_base]

omit [DecidableEq F] in
/-- **`x ∘ [n] − x(n • P)` vanishes at `P`**, at every affine `P` that is not `n`-torsion.

The `x`-coordinate formula `x(n • P) = Φₙ(x)/ΨSqₙ(x)` — merged at every index with `(2 : F) ≠ 0`
(`nsmul_eq_some_omegaY_of_ΨSq_ne_zero`, `EllipticCurves.Torsion.NsmulYPeriodic`) — read through the
presentation `x ∘ [n] = Φₙ(genX)/ΨSqₙ(genX)` (`mulByNEndo_genX_eq_ΦDivΨSq`,
`EllipticCurves.FunctionField.MulByNYCoordFormula`).  ⚠️ The general-`n` counterpart of
`ord_mulByTwoCoordHom_XClass_pos`, and the same argument: numerator vanishes, denominator does
not. -/
theorem ord_mulByNCoordHom_XClass_pos (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (hT : Transcendental F (n • genericPoint (W := W)).xCoord) (h : W.Equation x y)
    (hΨ : (W.ΨSq (n : ℤ)).eval x ≠ 0) :
    0 < ord (pointClosedPoint h)
      (mulByNCoordHom n hT (XClass W ((W.Φ (n : ℤ)).eval x / (W.ΨSq (n : ℤ)).eval x))) := by
  refine ord_pos_of_eq_evalEval_div h ?_
    (n := C (W.Φ (n : ℤ) - C ((W.Φ (n : ℤ)).eval x / (W.ΨSq (n : ℤ)).eval x) * W.ΨSq (n : ℤ)))
    (d := C (W.ΨSq (n : ℤ))) ?_ ?_ ?_
  · exact fun hz => XClass_ne_zero (W' := W) _
      (mulByNCoordHom_injective n hT (by rw [hz, map_zero]))
  · rw [mulByNCoordHom_XClass, mulByNEndo_genX_eq_ΦDivΨSq h2 hn]
    simp only [Polynomial.map_C, coe_mapRingHom, evalEval_C, Polynomial.map_sub,
      Polynomial.map_mul, eval_sub, eval_mul, eval_C, map_div₀, aeval_def, eval₂_eq_eval_map]
    have hB : eval (genX W) (Polynomial.map (algebraMap F W.FunctionField) (W.ΨSq (n : ℤ))) ≠ 0 :=
      eval_map_genX_ne_zero (fun hz => hΨ (by rw [hz, eval_zero]))
    field_simp
  · simp only [evalEval_C, eval_sub, eval_mul, eval_C]
    field_simp
    ring
  · simpa only [evalEval_C] using hΨ

omit [DecidableEq F] in
/-- **`y ∘ [n] − y(n • P)` vanishes at `P`**, at every affine `P` that is not `n`-torsion.

The `y`-coordinate formula `y(n • P) = ωₙ(x, y)/(2 ψₙ(x, y)³)` — `omegaY`,
`EllipticCurves.Torsion.NsmulYCoord`, merged at every index — read through the presentation
`y ∘ [n] = ωₙ(genX, genY)/(2 ψₙ(genX, genY)³)` (`mulByNEndo_genY_eq_omegaY`,
`EllipticCurves.FunctionField.MulByNYCoordFormula`).

⚠️ **This is the step `#774` could not price at `n = 2` and `#1540` could not price at general
`n`**, and both times for the same reason: it wants the `ωₙ` half of the coordinate pair, not the
`Φₙ/ΨSqₙ` half.  That half has been merged at every index since PR #579 (`#1500`) and the module
docstring above said in as many words that *"nothing below consumes it"*.  Something does now. -/
theorem ord_mulByNCoordHom_YClass_pos (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (hT : Transcendental F (n • genericPoint (W := W)).xCoord) (h : W.Equation x y)
    (hψ : (W.ψ (n : ℤ)).evalEval x y ≠ 0) :
    0 < ord (pointClosedPoint h)
      (mulByNCoordHom n hT (YClass W (C (W.omegaY x y (n : ℤ))))) := by
  refine ord_pos_of_eq_evalEval_div h ?_
    (n := (if Even (n : ℤ) then 1 else W.ψ 2) * C (W.preΩ (n : ℤ))
      - W.ψ (n : ℤ) * C (C W.a₁ * W.Φ (n : ℤ) + C W.a₃ * W.ΨSq (n : ℤ))
      - C (C (W.omegaY x y (n : ℤ))) * (2 * W.ψ (n : ℤ) ^ 3))
    (d := 2 * W.ψ (n : ℤ) ^ 3) ?_ ?_ ?_
  · exact fun hz => YClass_ne_zero (W' := W) _
      (mulByNCoordHom_injective n hT (by rw [hz, map_zero]))
  · have hψg : ((W.ψ (n : ℤ)).map (mapRingHom (algebraMap F W.FunctionField))).evalEval
        (genX W) (genY W) ≠ 0 := by
      rw [← map_ψ]; exact ψ_gen_ne_zero hn
    have h2' : (2 : W.FunctionField) ≠ 0 := fun hz =>
      h2 ((algebraMap F W.FunctionField).injective (by rw [map_ofNat, map_zero]; exact hz))
    have hψ2g : ((W.ψ 2).map (mapRingHom (algebraMap F W.FunctionField))).evalEval
        (genX W) (genY W)
          = 2 * genY W + algebraMap F W.FunctionField W.a₁ * genX W
            + algebraMap F W.FunctionField W.a₃ := by
      rw [← map_ψ]
      simpa only [map_a₁, map_a₃] using
        ψ_two_evalEval (W := W.map (algebraMap F W.FunctionField)) (x := genX W) (y := genY W)
    have hd0 : (2 : F) * (W.ψ (n : ℤ)).evalEval x y ^ 3 ≠ 0 :=
      mul_ne_zero h2 (pow_ne_zero 3 hψ)
    rw [mulByNCoordHom_YClass, mulByNEndo_genY_eq_omegaY h2 hn, omegaY, omegaY]
    simp only [map_ψ, map_preΩ, map_Φ, map_ΨSq, map_a₁, map_a₃, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_ofNat, Polynomial.map_one, apply_ite, coe_mapRingHom, evalEval,
      eval_sub, eval_mul, eval_add, eval_pow, eval_C, eval_ofNat, eval_one, map_div₀,
      map_sub, map_mul, map_add, map_pow, map_ofNat, map_one] at hψg hψ2g ⊢
    rw [hψ2g]
    field_simp
  · have hd0 : (2 : F) * (W.ψ (n : ℤ)).evalEval x y ^ 3 ≠ 0 :=
      mul_ne_zero h2 (pow_ne_zero 3 hψ)
    rw [omegaY]
    simp only [evalEval, eval_sub, eval_mul, eval_add, eval_pow, eval_C, eval_ofNat, apply_ite,
      eval_one, Polynomial.eval_one]
    field_simp
    rw [show Polynomial.eval x (Polynomial.eval (Polynomial.C y) (W.ψ 2))
        = 2 * y + W.a₁ * x + W.a₃ from ψ_two_evalEval]
    split_ifs <;> ring
  · simp only [evalEval, eval_mul, eval_pow, eval_ofNat]
    exact mul_ne_zero h2 (pow_ne_zero 3 hψ)

omit [DecidableEq F] in
/-- **`x ∘ [n]` is regular at an affine point that is not `n`-torsion**: its denominator
`ΨSqₙ(x)` does not vanish there.  The general-`n` form of `ord_mulByTwoEndo_genX_nonneg`. -/
theorem ord_mulByNEndo_genX_nonneg (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (hT : Transcendental F (n • genericPoint (W := W)).xCoord) (h : W.Equation x y)
    (hΨ : (W.ΨSq (n : ℤ)).eval x ≠ 0) :
    0 ≤ ord (pointClosedPoint h) (mulByNEndo n hT (genX W)) := by
  have hΨp : W.ΨSq (n : ℤ) ≠ 0 := fun hz => hΨ (by rw [hz, eval_zero])
  have hΨ0 : ord (pointClosedPoint h)
      (((W.ΨSq (n : ℤ)).map (algebraMap F W.FunctionField)).eval (genX W)) = 0 := by
    have hnn := ord_eval_map_genX_nonneg (W := W) (pointClosedPoint h) (W.ΨSq (n : ℤ))
    have hnp : ¬ 0 < ord (pointClosedPoint h)
        (((W.ΨSq (n : ℤ)).map (algebraMap F W.FunctionField)).eval (genX W)) := by
      rw [ord_eval_map_genX_pos_iff h hΨp]
      exact hΨ
    omega
  have hΦ := ord_eval_map_genX_nonneg (W := W) (pointClosedPoint h) (W.Φ (n : ℤ))
  rw [mulByNEndo_genX_eq_ΦDivΨSq h2 hn, aeval_def, aeval_def, eval₂_eq_eval_map,
    eval₂_eq_eval_map, ord_div _ (eval_map_genX_ne_zero (W.Φ_ne_zero (n : ℤ)))
      (eval_map_genX_ne_zero hΨp), hΨ0]
  omega

omit [DecidableEq F] in
/-- **The crux: `[n]` on places is `[n]` on points at an affine point that is not `n`-torsion.**

The general-`n` form of `comapProjPointTwo_pointClosedPoint`
(`EllipticCurves.FunctionField.MulByTwoFibreAffine`), with the doubling coordinates `addX`/`addY`
replaced by `Φₙ(x)/ΨSqₙ(x)` and `ωₙ`.  The argument is that file's, unchanged: the contracted place
is not `none` because `x ∘ [n]` is regular here while `x` has a double pole at infinity; and any
`g : F[W]` with `ord_P ([n]∗ g) > 0` lies in the contracted prime, by `divisorProj_mulByNEndo_apply`
against `ramificationIdxN_pos`.  Applied to the two generators of the closed point of `n • P`, that
puts a **maximal** ideal inside a prime one, so the two are equal. -/
theorem comapProjPointN_pointClosedPoint_of_ΨSq_ne_zero (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0)
    (hT : Transcendental F (n • genericPoint (W := W)).xCoord) (hns : W.Nonsingular x y)
    (hΨ : (W.ΨSq (n : ℤ)).eval x ≠ 0)
    (h' : W.Equation ((W.Φ (n : ℤ)).eval x / (W.ΨSq (n : ℤ)).eval x) (W.omegaY x y (n : ℤ))) :
    comapProjPointN n hT (some (pointClosedPoint hns.left))
      = some (pointClosedPoint h') := by
  have h := hns.left
  have hψ : (W.ψ (n : ℤ)).evalEval x y ≠ 0 := fun hz =>
    hΨ (by rw [← ψ_sq_evalEval h, hz]; ring)
  have hX := ord_mulByNCoordHom_XClass_pos h2 hn hT h hΨ
  have hY := ord_mulByNCoordHom_YClass_pos h2 hn hT h hψ
  cases hq : comapProjPointN n hT (some (pointClosedPoint h)) with
  | none =>
    exfalso
    have hkey := divisorProj_mulByNEndo_apply n hT (f := genX W) genX_ne_zero
      (some (pointClosedPoint h))
    rw [divisorProj_apply_some, hq, divisorProj_apply_none, ordInfty_genX] at hkey
    have hpos := ramificationIdxN_pos n hT (some (pointClosedPoint h))
    have hnn := ord_mulByNEndo_genX_nonneg h2 hn hT h hΨ
    rw [hkey] at hnn
    nlinarith [hpos, hnn]
  | some v =>
    have hmem : ∀ g : W.CoordinateRing, g ≠ 0 →
        0 < ord (pointClosedPoint h) (mulByNCoordHom n hT g) → g ∈ v.asIdeal := by
      intro g hg hgpos
      have hkey := divisorProj_mulByNEndo_apply n hT (f := genPsi W g)
        (fun hz => hg ((injective_iff_map_eq_zero _).mp
          (IsFractionRing.injective W.CoordinateRing W.FunctionField) _ hz))
        (some (pointClosedPoint h))
      rw [divisorProj_apply_some, hq, divisorProj_apply_some, genPsi,
        mulByNEndo_algebraMap] at hkey
      have hpos := ramificationIdxN_pos n hT (some (pointClosedPoint h))
      rw [hkey] at hgpos
      refine (ord_algebraMap_pos_iff v hg).1 ?_
      nlinarith [hpos, hgpos]
    have hle : (pointClosedPoint h').asIdeal ≤ v.asIdeal := by
      rw [pointClosedPoint_asIdeal, XYIdeal, Ideal.span_le]
      rintro g (rfl | rfl)
      · exact hmem _ (XClass_ne_zero _) hX
      · exact hmem _ (YClass_ne_zero _) hY
    have hmax : (pointClosedPoint h').asIdeal.IsMaximal :=
      Ideal.IsPrime.isMaximal (pointClosedPoint h').isPrime (pointClosedPoint h').ne_bot
    exact congrArg some (HeightOneSpectrum.ext (hmax.eq_of_le v.isPrime.ne_top hle).symm)

omit [DecidableEq F] in
/-- **`x ∘ [n]` has a pole at every affine `n`-torsion point.**  At a root of `ΨSqₙ` the
denominator of `Φₙ/ΨSqₙ` vanishes and the numerator does not, because the two are coprime —
`isCoprime_Φ_ΨSq` (`EllipticCurves.Torsion.CoprimeAdjacent`), at **every** `n : ℤ` over a field
with `(2 : F) ≠ 0`.  The general-`n` form of `ord_mulByTwoEndo_genX_neg`. -/
theorem ord_mulByNEndo_genX_neg (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (hT : Transcendental F (n • genericPoint (W := W)).xCoord) (h : W.Equation x y)
    (hx : (W.ΨSq (n : ℤ)).eval x = 0) :
    ord (pointClosedPoint h) (mulByNEndo n hT (genX W)) < 0 := by
  have hΦx : (W.Φ (n : ℤ)).eval x ≠ 0 :=
    eval_Φ_ne_zero_of_isCoprime (isCoprime_Φ_ΨSq h2 (n : ℤ)) hx
  have hΦ0 : ord (pointClosedPoint h)
      (((W.Φ (n : ℤ)).map (algebraMap F W.FunctionField)).eval (genX W)) = 0 := by
    have hnn := ord_eval_map_genX_nonneg (W := W) (pointClosedPoint h) (W.Φ (n : ℤ))
    have hnp : ¬ 0 < ord (pointClosedPoint h)
        (((W.Φ (n : ℤ)).map (algebraMap F W.FunctionField)).eval (genX W)) := by
      rw [ord_eval_map_genX_pos_iff h (W.Φ_ne_zero (n : ℤ))]
      exact hΦx
    omega
  have hΨ0 : 0 < ord (pointClosedPoint h)
      (((W.ΨSq (n : ℤ)).map (algebraMap F W.FunctionField)).eval (genX W)) :=
    (ord_eval_map_genX_pos_iff h (W.ΨSq_ne_zero hn)).2 hx
  rw [mulByNEndo_genX_eq_ΦDivΨSq h2 hn, aeval_def, aeval_def, eval₂_eq_eval_map,
    eval₂_eq_eval_map, ord_div _ (eval_map_genX_ne_zero (W.Φ_ne_zero (n : ℤ)))
      (eval_map_genX_ne_zero (W.ΨSq_ne_zero hn)), hΦ0]
  omega

omit [DecidableEq F] in
/-- **`[n]` contracts every affine `n`-torsion place to the place at infinity.**

The affine half of *"`[n]` maps `E[n]` to `O`"*, read on places, and the general-`n` form of
`comapProjPointTwo_pointClosedPoint_of_eval_Ψ₂Sq_eq_zero`
(`EllipticCurves.FunctionField.MulByTwoFibreInfinity`).  `x ∘ [n]` has a pole here, `x` has none at
any affine place, and the ramification index is positive, so the contracted place cannot be
affine. -/
theorem comapProjPointN_pointClosedPoint_of_eval_ΨSq_eq_zero (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0)
    (hT : Transcendental F (n • genericPoint (W := W)).xCoord) (h : W.Equation x y)
    (hx : (W.ΨSq (n : ℤ)).eval x = 0) :
    comapProjPointN n hT (some (pointClosedPoint h)) = none := by
  have hkey := divisorProj_mulByNEndo_apply n hT (f := genX W) genX_ne_zero
    (some (pointClosedPoint h))
  rw [divisorProj_apply_some] at hkey
  cases hq : comapProjPointN n hT (some (pointClosedPoint h)) with
  | none => rfl
  | some v =>
    exfalso
    rw [hq, divisorProj_apply_some] at hkey
    have hlt := ord_mulByNEndo_genX_neg h2 hn hT h hx
    have hge : (0 : ℤ) ≤ ord v (genX W) := by
      rw [genX, genPsi]
      exact ord_algebraMap_nonneg v _
    have hnn : (0 : ℤ) ≤ ramificationIdxN n hT (some (pointClosedPoint h)) * ord v (genX W) :=
      mul_nonneg (ramificationIdxN_pos n hT _).le hge
    omega

/-- **The place contraction of `[n]∗` is `[n]` on points, on the whole rational locus, at every `n`
with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`.**

```
comapProjPointN n h (projPointOfPoint P) = projPointOfPoint (n • P)
```

with no case hypothesis on `P` and no `3`-smoothness — **`#1540` item 2**, and the statement this
file was written around.  The three cases are `comapProjPointN_none_of_ne_zero`
(`EllipticCurves.FunctionField.MulByNPlaceComposition`, `P = O`),
`comapProjPointN_pointClosedPoint_of_eval_ΨSq_eq_zero` (`P` affine `n`-torsion) and
`comapProjPointN_pointClosedPoint_of_ΨSq_ne_zero` (`P` affine, not `n`-torsion).

⚠️ `((n : ℤ) : F) ≠ 0` is what **this route** needs, and removing it is **open, not closed**.
Every branch's proof consumes it — `natDegree_ΨSq` needs the leading coefficient `n` invertible
(`ord_mulByNEndo_genX_nonneg`, `ord_mulByNEndo_genX_neg`), `mulByNEndo_genX_eq_ΦDivΨSq` and
`mulByNEndo_genY_eq_omegaY` take it, and the `P = O` branch inherits it from the pole count — and
the *statement* asserts nothing about any order.
⚠️ **This paragraph used to read *"`((n : ℤ) : F) ≠ 0` is **not** removable and is not an artefact
of the route: at `n = char F` the pole order at infinity is `-2n` or `-2n²` rather than `-2` and
`e_∞ = 1` is false"*.  Both facts are true and **neither is about this statement.**  What
`EllipticCurves.FunctionField.MulByNPlaceComposition` records against
`ramificationIdxN_none_of_ne_zero` is that `e_∞ = 1` fails; `comapProjPointN_none_of_ne_zero` — the
branch consumed here — carries no falsity claim at `n = char F` and never has.  ⚠️ Indeed
`placeOf_comapProjPointN` (`EllipticCurves.FunctionField.MulByNPlacePullback`) makes the contracted
place the one *lying under*, `{f : ord_P ([n]∗ f) > 0}`, and `([n]∗ f)` vanishes at `P` exactly when
`f` vanishes at `[n] P` — **separability plays no role in that**.  So the sharpness argument that
does bound `ramificationIdxN_eq_one_…_of_ne_zero` below points the other way here.

⚠️ `comapProjPointN_projPointOfPoint_of_smooth` above is **not** deleted.  It is an independent
route — the composition ladder, which evaluates no division polynomial — and the `example` below
compiles the containment rather than asserting it. -/
theorem comapProjPointN_projPointOfPoint_of_ne_zero (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0)
    (hT : Transcendental F (n • genericPoint (W := W)).xCoord) (P : W.Point) :
    comapProjPointN n hT (projPointOfPoint W P) = projPointOfPoint W (n • P) := by
  rcases P with _ | ⟨x, y, hns⟩
  · rw [← Point.zero_def, smul_zero, projPointOfPoint_zero]
    exact comapProjPointN_none_of_ne_zero h2 hn hT
  · by_cases hΨ : (W.ΨSq (n : ℤ)).eval x = 0
    · have hψ : (W.ψ (n : ℤ)).evalEval x y = 0 := by
        have := ψ_sq_evalEval (W := W) (x := x) (y := y) hns.left (n := (n : ℤ))
        rw [hΨ] at this
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      have hzero : (n : ℕ) • Point.some x y hns = 0 :=
        (nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic h2 hns n).2 hψ
      rw [hzero, projPointOfPoint_zero, projPointOfPoint_some]
      exact comapProjPointN_pointClosedPoint_of_eval_ΨSq_eq_zero h2 hn hT hns.left hΨ
    · obtain ⟨h', hP⟩ := nsmul_eq_some_omegaY_of_ΨSq_ne_zero h2 hns hΨ
      rw [hP, projPointOfPoint_some, projPointOfPoint_some]
      exact comapProjPointN_pointClosedPoint_of_ΨSq_ne_zero h2 hn hT hns hΨ h'.left

/-- **`P ⊕ R` lies over `n • P`, for every `R ∈ E[n]`**, at every `n` with `(2 : F) ≠ 0` and
`((n : ℤ) : F) ≠ 0`.  The general-`n` form of `comapProjPointN_add_torsion_of_smooth`. -/
theorem comapProjPointN_add_torsion_of_ne_zero (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) {S P : W.Point} (hP : n • P = S)
    (R : W.torsion n) :
    comapProjPointN n h (projPointOfPoint W (P + R)) = projPointOfPoint W S := by
  rw [comapProjPointN_projPointOfPoint_of_ne_zero h2 hn h, smul_add, hP,
    mem_torsion_iff.mp R.2, add_zero]

/-! ### The containment of the `3`-smooth layer, compiled

⚠️ `3`-smoothness together with `(2 : F) ≠ 0`, `(3 : F) ≠ 0` and `n ≠ 0` forces
`((n : ℤ) : F) ≠ 0` (`Nat.intCast_ne_zero_of_smooth`, `EllipticCurves.Torsion.ThreePrimary`), so
every `_of_smooth` statement in this file is a **corollary** of its `_of_ne_zero` companion.  The
`example`s below restate the two above verbatim and prove them from the general layer, so the
containment is machine-checked rather than claimed; the four over `F̄` are restated the same way at
the end of that section.  The converse fails: `n = 14` satisfies `((n : ℤ) : F) ≠ 0` in
characteristic `0` and is not `3`-smooth. -/

/-- **`comapProjPointN_projPointOfPoint_of_smooth` is a corollary of the general form** — its
statement verbatim, proved from `comapProjPointN_projPointOfPoint_of_ne_zero`. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (P : W.Point) :
    comapProjPointN n h (projPointOfPoint W P) = projPointOfPoint W (n • P) :=
  comapProjPointN_projPointOfPoint_of_ne_zero h2 (Nat.intCast_ne_zero_of_smooth h2 h3 hn hfac) h P

/-- **`comapProjPointN_add_torsion_of_smooth` is a corollary of the general form** — its statement
verbatim, proved from `comapProjPointN_add_torsion_of_ne_zero`. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) {S P : W.Point} (hP : n • P = S)
    (R : W.torsion n) :
    comapProjPointN n h (projPointOfPoint W (P + R)) = projPointOfPoint W S :=
  comapProjPointN_add_torsion_of_ne_zero h2 (Nat.intCast_ne_zero_of_smooth h2 h3 hn hfac) h hP R

/-! ### The fibre over `F̄`

⚠️ `[IsAlgClosed F]` enters twice in this section, independently: once so that every place is
rational and `∑ e_p · f_p` collapses to `∑ e_p` (`sum_ramificationIdxN_of_smooth`), and once so that
`[n]` is surjective on points (`nsmul_surjective_of_smooth`) and the coset exists at all.  Neither
use is removable by progress on the other. -/

section IsAlgClosed

variable [IsAlgClosed F]

omit [DecidableEq F] in
/-- **At most `n²` places lie over any place**, at every `3`-smooth `n ≠ 0` with `(2 : F) ≠ 0` and
`(3 : F) ≠ 0` over `F̄`: `n²` positive indices summing to `n²`
(`sum_ramificationIdxN_of_smooth` against `ramificationIdxN_pos`).  The
general-`n` form of `card_fibre_comapProjPointTwo_le_four`. -/
theorem card_fibre_comapProjPointN_le_sq (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (q : ProjPoint W) :
    (finite_comapProjPointN_preimage_singleton n h q).toFinset.card ≤ n ^ 2 := by
  classical
  rw [Finset.card_eq_sum_ones, ← sum_ramificationIdxN_of_smooth h2 h3 hn hfac h q]
  exact Finset.sum_le_sum fun p _ => by have := ramificationIdxN_pos n h p; omega

omit [DecidableEq F] in
/-- **At most `n²` places lie over any place, at every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`
over `F̄`** — the
general-`n` form of `card_fibre_comapProjPointN_le_sq`, and `n²` positive indices summing to `n²`
by `sum_ramificationIdxN_of_ne_zero` (`EllipticCurves.FunctionField.MulByNInertia`) against
`ramificationIdxN_pos`, exactly as at a `3`-smooth index.

⚠️ **This is the only one of this file's eight `3`-smooth statements that lifts**, and the reason is
worth stating rather than leaving to be rediscovered.  It is the only one whose proof does not pass
through `comapProjPointN_projPointOfPoint_of_smooth`; see the section below for what the other
seven are actually gated on, which is **not** the torsion count and **not** the degree. -/
theorem card_fibre_comapProjPointN_le_sq_of_ne_zero (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : (n : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (q : ProjPoint W) :
    (finite_comapProjPointN_preimage_singleton n h q).toFinset.card ≤ n ^ 2 := by
  classical
  rw [Finset.card_eq_sum_ones, ← sum_ramificationIdxN_of_ne_zero h2 hn h q]
  exact Finset.sum_le_sum fun p _ => by have := ramificationIdxN_pos n h p; omega

omit [DecidableEq F] in
/-- **At most `25` places lie over any place, for `[5]∗` over `F̄`** — the bound at the first index
outside `{2, 3}`, named so that it can be cited.  ⚠️ The matching *equality* is **not** available at
`n = 5`, and the section below says exactly why: the `≥` half needs the place contraction, not the
torsion count. -/
theorem card_fibre_comapProjPointN_le_sq_five (h2 : (2 : F) ≠ 0) (h5 : (5 : F) ≠ 0)
    (q : ProjPoint W) :
    (finite_comapProjPointN_preimage_singleton 5
      (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2
        (by simpa using h5)) q).toFinset.card ≤ 5 ^ 2 :=
  card_fibre_comapProjPointN_le_sq_of_ne_zero h2 (by exact_mod_cast h5) _ q

/-! ### ⚠️ The seven statements that did NOT lift, and the measurement that said why — **paid**

⚠️ **This section used to be a gate list and is now a history.**  It read, of
`comapProjPointN_projPointOfPoint_of_smooth`, `comapProjPointN_add_torsion_of_smooth`,
`card_fibre_comapProjPointN_projPointOfPoint`, `fibre_comapProjPointN_eq_range`,
`ramificationIdxN_eq_one_of_comapProjPointN_eq_projPointOfPoint`,
`pullbackDivisorN_single_projPointOfPoint` and `pullbackDivisorN_single_eq_sum_torsion`:

> *"Every one of them passes through `comapProjPointN_two_pow_mul_three_pow_projPointOfPoint` — the
> double induction at `:157` — and that is a composition ladder, not a hypothesis. … ⚠️ **there the
> ladder had a replacement and here it does not.** … A general-`n` proof needs the same case
> analysis run against `Φₙ/ΨSqₙ`, i.e. against `nMulRatFunc_eq_ΦDivΨSq`
> (`EllipticCurves.FunctionField.MulByNXCoordFormula`), at the level of places rather than of
> points. ⚠️ **That is new mathematics, and it is `#1540` item 2.**"*

**Every clause of that is true, the diagnosis was exactly right, and the work it named has been
done** — `comapProjPointN_projPointOfPoint_of_ne_zero` above, with the case analysis run against
`Φₙ/ΨSqₙ` and `ωₙ` at the level of places, and the six consumers after it.  All seven now have
`_of_ne_zero` companions reaching every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`, and the
`_of_smooth` forms are kept as independent routes with the containment compiled by `example`.

### What the measurement got right, and the one thing it did not

* **Right, and load-bearing**: the ladder itself is not liftable at any hypotheses, so the general
  proof had to be a *different proof* rather than a weakening of this one.  It is:
  `comapProjPointN_two_pow_mul_three_pow_projPointOfPoint` is consumed by nothing in the general
  layer above — its only consumer anywhere is `comapProjPointN_projPointOfPoint_of_smooth`, whose
  one-line body is exactly that call.
* **Right**: none of `#293`'s count, `#1213`'s degree, `#268` or `hprin` (`#962`) is a gate.  The
  general proof consumes the count only in the *fibre* statements, exactly where the `3`-smooth
  ones consume `card_torsion_eq_sq_of_smooth`, and the contraction itself consumes none of the four.
* ⚠️ **Incomplete**: it named `nMulRatFunc_eq_ΦDivΨSq` — the `x`-half — as the input.  The `x`-half
  alone does not close the affine non-torsion branch: that branch needs **both** generators of the
  closed point of `n • P` to vanish, so it needs the `y`-half too.  That is `omegaY`
  (`EllipticCurves.Torsion.NsmulYCoord`) and `mulByNEndo_genY_eq_omegaY`
  (`EllipticCurves.FunctionField.MulByNYCoordFormula`), which is the **one import this file gained**
  (`155 → 156` modules in its transitive closure; **nothing imports this file**, so no other
  module's closure moves at all).
  The module docstring above says of the `ωₙ` formula that *"nothing below consumes it"*; that
  sentence was true when written and `ord_mulByNCoordHom_YClass_pos` is what makes it false.
* ⚠️ **Also unnamed**: the affine `n`-torsion branch needs `Φₙ` and `ΨSqₙ` to have no common root,
  which is `isCoprime_Φ_ΨSq` (`EllipticCurves.Torsion.CoprimeAdjacent`, every `n : ℤ` over a field
  with `(2 : F) ≠ 0`).  At `n = 2` that role is played by `IsUnit Δ` through
  `eval_Φ_two_ne_zero_of_eval_Ψ₂Sq_eq_zero`; at general `n` the coprimality statement is the right
  tool and it was already merged.

### The four `MulByNPlaceComposition` sites, and why they were never on this gate

⚠️ **This section used to end by counting the gate at eleven rather than seven**, adding
`comapProjPointN_none_of_smooth`, `ramificationIdxN_none_of_smooth`, `ordInfty_mulByNEndo_of_smooth`
and `ordInfty_mulByNEndo_genX_of_smooth` (`EllipticCurves.FunctionField.MulByNPlaceComposition`) on
the ground that each opens with the identical `Nat.exists_eq_two_pow_mul_three_pow` step and lands
the double inductions `comapProjPointN_two_pow_mul_three_pow_none` /
`ramificationIdxN_two_pow_mul_three_pow_none`.  **That measurement was correct when it was made and
those four came off the gate first** (`#1540` item 1, PR #599), by the **pole order** and not by any
case split: `x(n • 𝒫) = Φₙ(genX)/ΨSqₙ(genX)` has a pole of order `2n²` over one of order
`2(n² - 1)`, so `ordInfty ([n]∗ genX) = -2`, and running `divisorProj_mulByNEndo_apply` backwards
against that **negative** order forces the contracted place to be `none`.

⚠️ **That argument transfers to nothing here, and this file's prediction that it would not was
right.**  At an affine rational point `genX` has no pole and hence no sign to exploit.  What closes
the affine branches instead is the *other* direction of the same machinery — `ord_P ([n]∗ g) > 0`
puts `g` in the contracted prime — which needs the coordinate formulas and not an order bound.
⚠️ So item 1 falling to the pole order really was no evidence about item 2; the two were solved by
different arguments, and only the second needed `ωₙ`.

⚠️ One prediction of the retired text is worth keeping and is unchanged:
`ramificationIdxN_none_of_smooth` carries its `3`-smoothness as *separability* work — with
`(2 : F) ≠ 0` and `(3 : F) ≠ 0` it is what forces `char F ∤ n` — so the general form of that one
wants a hypothesis on `n` in the **statement** and not merely a better proof.
`ramificationIdxN_none_of_ne_zero` does carry `((n : ℤ) : F) ≠ 0`, and it is sharp: at
`n = char F > 2` the index is `n` or `n²`, not `1`.  ⚠️ **That sharpness bounds the ramification
and fibre statements of this file and no more**: `ramificationIdxN_eq_one_…_of_ne_zero` is false at
`n = char F` because `O` is a rational point, and the fibre count goes with it because
`#E[p] ≤ p < p²`.  ⚠️ **This sentence used to say *"The same sharpness bounds everything in this
section"*, and it does not**: for the contraction and `comapProjPointN_add_torsion_of_ne_zero`
`((n : ℤ) : F) ≠ 0` is the route's, and dropping it is open — see the sharpness paragraph on
`comapProjPointN_projPointOfPoint_of_ne_zero`.
-/

omit [DecidableEq F] in
/-- **The fibre of `[n]` over any rational point has exactly `n²` elements**, at every `3`-smooth
`n ≠ 0` with `(2 : F) ≠ 0` and `(3 : F) ≠ 0` over `F̄`.

`≥ n²` is the coset `{ P ⊕ R : R ∈ E[n] }` for a `P` with `n • P = S` (`exists_nsmul_eq_of_smooth`),
which has `n²` distinct elements by `card_torsion_eq_sq_of_smooth` and
`projPointOfPoint_add_injective` and lies in the fibre by `comapProjPointN_add_torsion_of_smooth`;
`≤ n²` is `card_fibre_comapProjPointN_le_sq`. -/
theorem card_fibre_comapProjPointN_projPointOfPoint (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (S : W.Point) :
    (finite_comapProjPointN_preimage_singleton n h (projPointOfPoint W S)).toFinset.card
      = n ^ 2 := by
  classical
  haveI := W.finite_torsion_of_smooth h2 h3 hn hfac
  haveI := Fintype.ofFinite (W.torsion n)
  obtain ⟨P, hP⟩ := exists_nsmul_eq_of_smooth h2 hn hfac S
  refine le_antisymm (card_fibre_comapProjPointN_le_sq h2 h3 hn hfac h _) ?_
  have hcard : Fintype.card (W.torsion n) = n ^ 2 := by
    rw [← Nat.card_eq_fintype_card, card_torsion_eq_sq_of_smooth h2 h3 hn hfac]
  rw [← hcard, ← Finset.card_univ]
  exact Finset.card_le_card_of_injOn (fun R => projPointOfPoint W (P + R))
    (fun R _ => (Set.Finite.mem_toFinset _).2
      (comapProjPointN_add_torsion_of_smooth h2 h3 hn hfac h hP R))
    (Set.injOn_of_injective (projPointOfPoint_add_injective n P))

/-- **The fibre of `[n]` over a rational point *is* the coset `{ P ⊕ R : R ∈ E[n] }`**, at every
`3`-smooth `n ≠ 0` with `(2 : F) ≠ 0` and `(3 : F) ≠ 0` over `F̄`, for any `P` with `n • P = S`.

The set-theoretic half of the fibre description at every `3`-smooth `n`.  The inclusion `⊇` is
`comapProjPointN_add_torsion_of_smooth`; the reverse is pure counting — `n²` distinct elements
inside an `n²`-element set, with no further geometry.

Stated with `Set.range` rather than a `Finset.image` because `ProjPoint W` carries no
`DecidableEq`, and baking a classical one into the statement would restrict who can apply it. -/
theorem fibre_comapProjPointN_eq_range (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) {S P : W.Point} (hP : n • P = S) :
    comapProjPointN n h ⁻¹' {projPointOfPoint W S}
      = Set.range fun R : W.torsion n => projPointOfPoint W (P + R) := by
  classical
  haveI := W.finite_torsion_of_smooth h2 h3 hn hfac
  haveI := Fintype.ofFinite (W.torsion n)
  have hfin := finite_comapProjPointN_preimage_singleton n h (projPointOfPoint W S)
  have hsub : (Set.range fun R : W.torsion n => projPointOfPoint W (P + R))
      ⊆ comapProjPointN n h ⁻¹' {projPointOfPoint W S} := by
    rintro p ⟨R, rfl⟩
    exact comapProjPointN_add_torsion_of_smooth h2 h3 hn hfac h hP R
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ hfin).symm
  have hfibre : (comapProjPointN n h ⁻¹' {projPointOfPoint W S}).ncard = n ^ 2 := by
    rw [Set.ncard_eq_toFinset_card _ hfin]
    exact card_fibre_comapProjPointN_projPointOfPoint h2 h3 hn hfac h S
  have hcoset : (Set.range fun R : W.torsion n => projPointOfPoint W (P + R)).ncard = n ^ 2 := by
    rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective (projPointOfPoint_add_injective n P),
      card_torsion_eq_sq_of_smooth h2 h3 hn hfac]
  omega

omit [DecidableEq F] in
/-- **`[n]` is unramified over every rational point**, at every `3`-smooth `n ≠ 0` with
`(2 : F) ≠ 0` and `(3 : F) ≠ 0` over `F̄`: `n²` positive indices summing to `n²` are all `1`.

⚠️ This is *not* "`[n]` is unramified": a place lying over a closed point that is **not** the closed
point of an `F`-rational point is untouched.  See the module docstring.  ⚠️ Nor is it removable to a
general `n` **with no hypothesis on `n` at all**: `ramificationIdxN_none_of_ne_zero`
(`EllipticCurves.FunctionField.MulByNPlaceComposition`) is the sharp form at infinity, and its
`((n : ℤ) : F) ≠ 0` is load-bearing precisely because at `n = char F` the index there is `n` or
`n²` rather than `1`.  ⚠️ **The `3`-smoothness here is doing two jobs, not one**: that index
condition, which is genuinely needed, *and* the composition ladder, which is `#1540` item 2 and is
open.  This docstring used to cite `ramificationIdxN_none_of_smooth` for the characteristic-`p`
fact; that statement excludes `char F ∣ n` by its own hypotheses and so records nothing about it. -/
theorem ramificationIdxN_eq_one_of_comapProjPointN_eq_projPointOfPoint (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) {p : ProjPoint W} {S : W.Point}
    (hp : comapProjPointN n h p = projPointOfPoint W S) :
    ramificationIdxN n h p = 1 := by
  classical
  set s := (finite_comapProjPointN_preimage_singleton n h (projPointOfPoint W S)).toFinset with hs
  have hmem : p ∈ s := (Set.Finite.mem_toFinset _).2 hp
  have hcard : s.card = n ^ 2 := card_fibre_comapProjPointN_projPointOfPoint h2 h3 hn hfac h S
  have hsum : ∑ q ∈ s, (ramificationIdxN n h q).toNat = n ^ 2 :=
    sum_ramificationIdxN_of_smooth h2 h3 hn hfac h _
  have hsplit : (ramificationIdxN n h p).toNat
      + ∑ q ∈ s.erase p, (ramificationIdxN n h q).toNat = n ^ 2 := by
    rw [Finset.add_sum_erase _ (fun q => (ramificationIdxN n h q).toNat) hmem]
    exact hsum
  have hlow : (s.erase p).card ≤ ∑ q ∈ s.erase p, (ramificationIdxN n h q).toNat := by
    simpa using Finset.card_nsmul_le_sum (s.erase p) (fun q => (ramificationIdxN n h q).toNat) 1
      (fun q _ => by have := ramificationIdxN_pos n h q; omega)
  have hec : (s.erase p).card = n ^ 2 - 1 := by rw [Finset.card_erase_of_mem hmem, hcard]
  have hpos := ramificationIdxN_pos n h p
  have hone : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hn)
  omega

omit [DecidableEq F] in
/-- **The fibre description of `[n]∗` over a rational point**, at every `3`-smooth `n ≠ 0` with
`(2 : F) ≠ 0` and `(3 : F) ≠ 0` over `F̄`: `[n]∗(S) = ∑_{p ↦ S} (p)`, every coefficient `1`.

At `S = O` this is `comapProjPointN_none_of_smooth` and `ramificationIdxN_none_of_smooth`
(`EllipticCurves.FunctionField.MulByNPlaceComposition`) read as a divisor — or, more sharply,
their `_of_ne_zero` forms, which reach every `n` with `((n : ℤ) : F) ≠ 0` (PR #599); at an affine
`S` it is new at every index outside `{2, 3}`.  ⚠️ The `_of_smooth` citation is what this
statement's own hypotheses can consume, and it is why the two halves of the displayed identity
below do **not** have the same reach.  The two together give

```
[n]∗((S) − (O)) = ∑_{p ↦ S} (p) − ∑_{p ↦ O} (p).
```
-/
theorem pullbackDivisorN_single_projPointOfPoint (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (S : W.Point) :
    pullbackDivisorN n h (Finsupp.single (projPointOfPoint W S) (1 : ℤ))
      = ∑ p ∈ (finite_comapProjPointN_preimage_singleton n h
          (projPointOfPoint W S)).toFinset, Finsupp.single p (1 : ℤ) := by
  classical
  ext q
  have hrhs : (∑ p ∈ (finite_comapProjPointN_preimage_singleton n h
        (projPointOfPoint W S)).toFinset, Finsupp.single p (1 : ℤ)) q
      = if comapProjPointN n h q = projPointOfPoint W S then 1 else 0 := by
    rw [Finset.sum_apply', Finset.sum_congr rfl fun p _ => Finsupp.single_apply,
      Finset.sum_ite_eq' _ q fun _ => (1 : ℤ)]
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]
  rw [pullbackDivisorN_apply, hrhs]
  by_cases hq : comapProjPointN n h q = projPointOfPoint W S
  · rw [hq, Finsupp.single_eq_same, mul_one,
      ramificationIdxN_eq_one_of_comapProjPointN_eq_projPointOfPoint h2 h3 hn hfac h hq, if_pos rfl]
  · rw [Finsupp.single_apply, if_neg fun hc => hq hc.symm, mul_zero, if_neg hq]

/-- **The fibre description in the shape a rung-4 consumer wants**, at every `3`-smooth `n ≠ 0`
with `(2 : F) ≠ 0` and `(3 : F) ≠ 0` over `F̄`: for any `P` with `n • P = S`,

```
[n]∗(S) = ∑_{R ∈ E[n]} (P ⊕ R).
```

Subtracting the same statement at `S = O` (where `P` may be taken to be `O`, so that the sum is
`∑_R (R)`) gives `[n]∗((S) − (O)) = ∑_{R ∈ E[n]} ((P ⊕ R) − (R))` — `#774`'s formula at every
`3`-smooth `n`.

The `[Fintype (W.torsion n)]` is carried in the statement rather than produced inside it: the sum
cannot be written without it, and pushing `Fintype.ofFinite` into a statement is the noncomputable
leak `#763` warns against.  `finite_torsion_of_smooth` supplies it at the point of use. -/
theorem pullbackDivisorN_single_eq_sum_torsion (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    [Fintype (W.torsion n)] (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) {S P : W.Point} (hP : n • P = S) :
    pullbackDivisorN n h (Finsupp.single (projPointOfPoint W S) (1 : ℤ))
      = ∑ R : W.torsion n, Finsupp.single (projPointOfPoint W (P + R)) (1 : ℤ) := by
  classical
  ext q
  rw [pullbackDivisorN_apply, Finset.sum_apply',
    Finset.sum_congr rfl fun R _ => Finsupp.single_apply]
  by_cases hq : comapProjPointN n h q = projPointOfPoint W S
  · obtain ⟨R₀, hR₀⟩ : q ∈ Set.range fun R : W.torsion n => projPointOfPoint W (P + R) := by
      rw [← fibre_comapProjPointN_eq_range h2 h3 hn hfac h hP]; exact hq
    rw [hq, Finsupp.single_eq_same, mul_one,
      ramificationIdxN_eq_one_of_comapProjPointN_eq_projPointOfPoint h2 h3 hn hfac h hq,
      Finset.sum_eq_single R₀ (fun R _ hRne => if_neg fun hc =>
        hRne (projPointOfPoint_add_injective n P (hc.trans hR₀.symm)))
      (fun hc => absurd (Finset.mem_univ R₀) hc), if_pos hR₀]
  · rw [Finsupp.single_apply, if_neg fun hc => hq hc.symm, mul_zero, Finset.sum_eq_zero]
    intro R _
    refine if_neg fun hc => hq ?_
    rw [← hc]
    exact comapProjPointN_add_torsion_of_smooth h2 h3 hn hfac h hP R

/-! ### The fibre over `F̄` at every `n` with `((n : ℤ) : F) ≠ 0`

⚠️ The two independent uses of `[IsAlgClosed F]` recorded at the head of this section are
**unchanged**: the general layer still needs every place rational
(`sum_ramificationIdxN_of_ne_zero`) and still needs `[n]`-surjectivity on points
(`nsmul_surjective_of_two_ne_zero`, `EllipticCurves.Torsion.TwoTorsionOrder`, at every `n ≠ 0` with
`(2 : F) ≠ 0`).  What changes is the *index* axis and nothing else. -/

omit [DecidableEq F] in
/-- **The fibre of `[n]` over any rational point has exactly `n²` elements**, at every `n` with
`(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` over `F̄`.

`≥ n²` is the coset `{ P ⊕ R : R ∈ E[n] }` for a `P` with `n • P = S`
(`nsmul_surjective_of_two_ne_zero`), which has `n²` distinct elements by `card_torsion_eq_sq`
(`EllipticCurves.Torsion.StructureGeneral`) and `projPointOfPoint_add_injective` and lies in the
fibre by `comapProjPointN_add_torsion_of_ne_zero`; `≤ n²` is
`card_fibre_comapProjPointN_le_sq_of_ne_zero`, which was general already. -/
theorem card_fibre_comapProjPointN_projPointOfPoint_of_ne_zero (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (S : W.Point) :
    (finite_comapProjPointN_preimage_singleton n h (projPointOfPoint W S)).toFinset.card
      = n ^ 2 := by
  classical
  have hn' : (n : F) ≠ 0 := by exact_mod_cast hn
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn'
  haveI := W.finite_torsion_of_intCast_ne_zero h2 hn'
  haveI := Fintype.ofFinite (W.torsion n)
  obtain ⟨P, hP⟩ := nsmul_surjective_of_two_ne_zero h2 hn0 S
  refine le_antisymm (card_fibre_comapProjPointN_le_sq_of_ne_zero h2 hn' h _) ?_
  have hcard : Fintype.card (W.torsion n) = n ^ 2 := by
    rw [← Nat.card_eq_fintype_card, card_torsion_eq_sq h2 hn']
  rw [← hcard, ← Finset.card_univ]
  exact Finset.card_le_card_of_injOn (fun R => projPointOfPoint W (P + R))
    (fun R _ => (Set.Finite.mem_toFinset _).2
      (comapProjPointN_add_torsion_of_ne_zero h2 hn h hP R))
    (Set.injOn_of_injective (projPointOfPoint_add_injective n P))

/-- **The fibre of `[n]` over a rational point *is* the coset `{ P ⊕ R : R ∈ E[n] }`**, at every `n`
with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` over `F̄`.  The general-`n` form of
`fibre_comapProjPointN_eq_range`; the inclusion `⊇` is `comapProjPointN_add_torsion_of_ne_zero` and
the reverse is pure counting. -/
theorem fibre_comapProjPointN_eq_range_of_ne_zero (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) {S P : W.Point} (hP : n • P = S) :
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
    exact card_fibre_comapProjPointN_projPointOfPoint_of_ne_zero h2 hn h S
  have hcoset : (Set.range fun R : W.torsion n => projPointOfPoint W (P + R)).ncard = n ^ 2 := by
    rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective (projPointOfPoint_add_injective n P),
      card_torsion_eq_sq h2 hn']
  omega

omit [DecidableEq F] in
/-- **`[n]` is unramified over every rational point**, at every `n` with `(2 : F) ≠ 0` and
`((n : ℤ) : F) ≠ 0` over `F̄`: `n²` positive indices summing to `n²` are all `1`.

⚠️ As at a `3`-smooth index, this is *not* "`[n]` is unramified" — a place over a closed point that
is not the closed point of an `F`-rational point is untouched.  ⚠️ And `((n : ℤ) : F) ≠ 0` is
**sharp**: at `n = char F` the index at infinity alone is `n` or `n²`
(`ramificationIdxN_none_of_ne_zero`, `EllipticCurves.FunctionField.MulByNPlaceComposition`). -/
theorem ramificationIdxN_eq_one_of_comapProjPointN_eq_projPointOfPoint_of_ne_zero
    (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) {p : ProjPoint W} {S : W.Point}
    (hp : comapProjPointN n h p = projPointOfPoint W S) :
    ramificationIdxN n h p = 1 := by
  classical
  have hn' : (n : F) ≠ 0 := by exact_mod_cast hn
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn'
  set s := (finite_comapProjPointN_preimage_singleton n h (projPointOfPoint W S)).toFinset with hs
  have hmem : p ∈ s := (Set.Finite.mem_toFinset _).2 hp
  have hcard : s.card = n ^ 2 :=
    card_fibre_comapProjPointN_projPointOfPoint_of_ne_zero h2 hn h S
  have hsum : ∑ q ∈ s, (ramificationIdxN n h q).toNat = n ^ 2 :=
    sum_ramificationIdxN_of_ne_zero h2 hn' h _
  have hsplit : (ramificationIdxN n h p).toNat
      + ∑ q ∈ s.erase p, (ramificationIdxN n h q).toNat = n ^ 2 := by
    rw [Finset.add_sum_erase _ (fun q => (ramificationIdxN n h q).toNat) hmem]
    exact hsum
  have hlow : (s.erase p).card ≤ ∑ q ∈ s.erase p, (ramificationIdxN n h q).toNat := by
    simpa using Finset.card_nsmul_le_sum (s.erase p) (fun q => (ramificationIdxN n h q).toNat) 1
      (fun q _ => by have := ramificationIdxN_pos n h q; omega)
  have hec : (s.erase p).card = n ^ 2 - 1 := by rw [Finset.card_erase_of_mem hmem, hcard]
  have hpos := ramificationIdxN_pos n h p
  have hone : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hn0)
  omega

omit [DecidableEq F] in
/-- **The fibre description of `[n]∗` over a rational point**, at every `n` with `(2 : F) ≠ 0` and
`((n : ℤ) : F) ≠ 0` over `F̄`: `[n]∗(S) = ∑_{p ↦ S} (p)`, every coefficient `1`.

⚠️ **Both halves of the displayed identity now have the same reach**, which was not true before:

```
[n]∗((S) − (O)) = ∑_{p ↦ S} (p) − ∑_{p ↦ O} (p).
```

At `S = O` this is `comapProjPointN_none_of_ne_zero` and `ramificationIdxN_none_of_ne_zero`
(`EllipticCurves.FunctionField.MulByNPlaceComposition`, `#1540` item 1) read as a divisor; at an
affine `S` it is this statement, off `#1540` item 2. -/
theorem pullbackDivisorN_single_projPointOfPoint_of_ne_zero (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (S : W.Point) :
    pullbackDivisorN n h (Finsupp.single (projPointOfPoint W S) (1 : ℤ))
      = ∑ p ∈ (finite_comapProjPointN_preimage_singleton n h
          (projPointOfPoint W S)).toFinset, Finsupp.single p (1 : ℤ) := by
  classical
  ext q
  have hrhs : (∑ p ∈ (finite_comapProjPointN_preimage_singleton n h
        (projPointOfPoint W S)).toFinset, Finsupp.single p (1 : ℤ)) q
      = if comapProjPointN n h q = projPointOfPoint W S then 1 else 0 := by
    rw [Finset.sum_apply', Finset.sum_congr rfl fun p _ => Finsupp.single_apply,
      Finset.sum_ite_eq' _ q fun _ => (1 : ℤ)]
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]
  rw [pullbackDivisorN_apply, hrhs]
  by_cases hq : comapProjPointN n h q = projPointOfPoint W S
  · rw [hq, Finsupp.single_eq_same, mul_one,
      ramificationIdxN_eq_one_of_comapProjPointN_eq_projPointOfPoint_of_ne_zero h2 hn h hq,
      if_pos rfl]
  · rw [Finsupp.single_apply, if_neg fun hc => hq hc.symm, mul_zero, if_neg hq]

/-- **The fibre description in the shape a rung-4 consumer wants**, at every `n` with
`(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` over `F̄`: for any `P` with `n • P = S`,

```
[n]∗(S) = ∑_{R ∈ E[n]} (P ⊕ R).
```

⚠️ This is `#774`'s formula at every `n` prime to the characteristic, and the last of the eleven
declarations `#1540` measured as blocked.  `[Fintype (W.torsion n)]` is carried in the statement
for the reason the `3`-smooth form gives; `finite_torsion_of_intCast_ne_zero`
(`EllipticCurves.Torsion.XSupport`) supplies it at the point of use, and needs neither
`[IsAlgClosed F]` nor `[W.IsElliptic]`. -/
theorem pullbackDivisorN_single_eq_sum_torsion_of_ne_zero (h2 : (2 : F) ≠ 0) {n : ℕ}
    [Fintype (W.torsion n)] (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) {S P : W.Point} (hP : n • P = S) :
    pullbackDivisorN n h (Finsupp.single (projPointOfPoint W S) (1 : ℤ))
      = ∑ R : W.torsion n, Finsupp.single (projPointOfPoint W (P + R)) (1 : ℤ) := by
  classical
  ext q
  rw [pullbackDivisorN_apply, Finset.sum_apply',
    Finset.sum_congr rfl fun R _ => Finsupp.single_apply]
  by_cases hq : comapProjPointN n h q = projPointOfPoint W S
  · obtain ⟨R₀, hR₀⟩ : q ∈ Set.range fun R : W.torsion n => projPointOfPoint W (P + R) := by
      rw [← fibre_comapProjPointN_eq_range_of_ne_zero h2 hn h hP]; exact hq
    rw [hq, Finsupp.single_eq_same, mul_one,
      ramificationIdxN_eq_one_of_comapProjPointN_eq_projPointOfPoint_of_ne_zero h2 hn h hq,
      Finset.sum_eq_single R₀ (fun R _ hRne => if_neg fun hc =>
        hRne (projPointOfPoint_add_injective n P (hc.trans hR₀.symm)))
      (fun hc => absurd (Finset.mem_univ R₀) hc), if_pos hR₀]
  · rw [Finsupp.single_apply, if_neg fun hc => hq hc.symm, mul_zero, Finset.sum_eq_zero]
    intro R _
    refine if_neg fun hc => hq ?_
    rw [← hc]
    exact comapProjPointN_add_torsion_of_ne_zero h2 hn h hP R

/-! ### The containment of the `3`-smooth layer over `F̄`, compiled

The five `example`s below restate the five `3`-smooth statements of this section verbatim and prove
each from its general companion, through `Nat.intCast_ne_zero_of_smooth`
(`EllipticCurves.Torsion.ThreePrimary`).  ⚠️ **Each carries its original's `omit` line, not the
ambient variable block's default** — three of the five originals `omit [DecidableEq F]`, and an
`example` that quietly keeps that instance restates something *weaker* than the theorem it claims
to subsume.  The signature strings match either way, so it is not visible to a textual check.

⚠️ `card_fibre_comapProjPointN_le_sq` gets none: it was
already subsumed by `card_fibre_comapProjPointN_le_sq_of_ne_zero` when that landed, and its
`(n : F) ≠ 0` is the nat-cast form. -/

omit [DecidableEq F] in
/-- **`card_fibre_comapProjPointN_projPointOfPoint` is a corollary of the general form.** -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (S : W.Point) :
    (finite_comapProjPointN_preimage_singleton n h (projPointOfPoint W S)).toFinset.card
      = n ^ 2 :=
  card_fibre_comapProjPointN_projPointOfPoint_of_ne_zero h2
    (Nat.intCast_ne_zero_of_smooth h2 h3 hn hfac) h S

/-- **`fibre_comapProjPointN_eq_range` is a corollary of the general form.** -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) {S P : W.Point} (hP : n • P = S) :
    comapProjPointN n h ⁻¹' {projPointOfPoint W S}
      = Set.range fun R : W.torsion n => projPointOfPoint W (P + R) :=
  fibre_comapProjPointN_eq_range_of_ne_zero h2 (Nat.intCast_ne_zero_of_smooth h2 h3 hn hfac) h hP

omit [DecidableEq F] in
/-- **`ramificationIdxN_eq_one_of_comapProjPointN_eq_projPointOfPoint` is a corollary of the
general form.** -/
example (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) {p : ProjPoint W} {S : W.Point}
    (hp : comapProjPointN n h p = projPointOfPoint W S) :
    ramificationIdxN n h p = 1 :=
  ramificationIdxN_eq_one_of_comapProjPointN_eq_projPointOfPoint_of_ne_zero h2
    (Nat.intCast_ne_zero_of_smooth h2 h3 hn hfac) h hp

omit [DecidableEq F] in
/-- **`pullbackDivisorN_single_projPointOfPoint` is a corollary of the general form.** -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (S : W.Point) :
    pullbackDivisorN n h (Finsupp.single (projPointOfPoint W S) (1 : ℤ))
      = ∑ p ∈ (finite_comapProjPointN_preimage_singleton n h
          (projPointOfPoint W S)).toFinset, Finsupp.single p (1 : ℤ) :=
  pullbackDivisorN_single_projPointOfPoint_of_ne_zero h2
    (Nat.intCast_ne_zero_of_smooth h2 h3 hn hfac) h S

/-- **`pullbackDivisorN_single_eq_sum_torsion` is a corollary of the general form.** -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    [Fintype (W.torsion n)] (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) {S P : W.Point} (hP : n • P = S) :
    pullbackDivisorN n h (Finsupp.single (projPointOfPoint W S) (1 : ℤ))
      = ∑ R : W.torsion n, Finsupp.single (projPointOfPoint W (P + R)) (1 : ℤ) :=
  pullbackDivisorN_single_eq_sum_torsion_of_ne_zero h2
    (Nat.intCast_ne_zero_of_smooth h2 h3 hn hfac) h hP

/-! ### Non-vacuity

⚠️ Every statement in this file carries `[IsDedekindDomain W.CoordinateRing]` and `[W.IsElliptic]`
on top of a non-constancy hypothesis, and the `F̄` block adds `[IsAlgClosed F]` and `3`-smoothness;
a theorem whose hypotheses could not all be met at once would be vacuous.  One curve on which the
whole chain elaborates, at an index outside `{2, 3}`, is committed rather than quoted.

⚠️ The non-constancy hypothesis is **produced**, never assumed:
`transcendental_xCoord_nsmul_of_smooth` at `n = 12`. -/

section Nonvacuity

/-! The certificate curve `y² + y = x³` is the shared `EllipticCurves.Fixture.y2AddYEqX3`, and the
base — algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here. -/

open EllipticCurves.Fixture

private noncomputable instance : DecidableEq AlgClosedQ := Classical.decEq _

private lemma exampleFibreTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleFibreThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

/-- ⚠️ `decide` does **not** close this: `Nat.primeFactors` goes through `Nat.primeFactorsList`,
whose `Decidable` instance gets stuck on `Nat.minFac`'s well-founded recursion. -/
private lemma smoothTwelveFibre : ∀ p ∈ Nat.primeFactors 12, p = 2 ∨ p = 3 := by
  intro p hp
  obtain ⟨hp1, hp2, -⟩ := Nat.mem_primeFactors.mp hp
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) hp2
  interval_cases p <;> revert hp1 hp2 <;> decide

example : IsDedekindDomain (y2AddYEqX3 AlgClosedQ).CoordinateRing := inferInstance

/-- **The contraction at `n = 12`, committed** — an index at which neither merged computation says
anything. -/
example (P : (y2AddYEqX3 AlgClosedQ).Point) :
    comapProjPointN 12 (transcendental_xCoord_nsmul_of_smooth (W := y2AddYEqX3 AlgClosedQ)
        exampleFibreTwo exampleFibreThree (by norm_num) smoothTwelveFibre)
      (projPointOfPoint (y2AddYEqX3 AlgClosedQ) P)
      = projPointOfPoint (y2AddYEqX3 AlgClosedQ) ((12 : ℕ) • P) :=
  comapProjPointN_projPointOfPoint_of_smooth exampleFibreTwo exampleFibreThree (by norm_num)
    smoothTwelveFibre _ P

/-- **`#{p ↦ S} = 144` at `n = 12`, committed** — the fibre count, on a genuine curve. -/
example (S : (y2AddYEqX3 AlgClosedQ).Point) :
    (finite_comapProjPointN_preimage_singleton 12
      (transcendental_xCoord_nsmul_of_smooth (W := y2AddYEqX3 AlgClosedQ) exampleFibreTwo
        exampleFibreThree (by norm_num) smoothTwelveFibre)
      (projPointOfPoint (y2AddYEqX3 AlgClosedQ) S)).toFinset.card = 144 := by
  have h144 := card_fibre_comapProjPointN_projPointOfPoint (W := y2AddYEqX3 AlgClosedQ)
      exampleFibreTwo
    exampleFibreThree (n := 12) (by norm_num) smoothTwelveFibre
    (transcendental_xCoord_nsmul_of_smooth (W := y2AddYEqX3 AlgClosedQ) exampleFibreTwo
      exampleFibreThree (by norm_num) smoothTwelveFibre) S
  norm_num at h144
  exact h144

private lemma exampleFibreFourteen : ((14 : ℕ) : AlgClosedQ) ≠ 0 := by
  have : ((14 : ℕ) : AlgClosedQ) = 14 := by push_cast; ring
  rw [this]; norm_num

/-- **`#{p ↦ q} ≤ 196` at `n = 14`, committed** — the bound at an index that is **even and not
`3`-smooth**, hence reachable by no `3`-smooth and no odd-`n` statement.

⚠️ This certificate is deliberately an *inequality*, and it used to say the matching equality
*"needs the place contraction at general `n`, which is `#1540` item 2 and is not gated on anything
merged"*.  That is paid: `card_fibre_comapProjPointN_projPointOfPoint_of_ne_zero` gives the
**equality** at this very index, and it is committed below.  The inequality is kept because it is
an independent route — it consumes only the fundamental identity, and no coordinate formula. -/
example (q : ProjPoint (y2AddYEqX3 AlgClosedQ)) :
    (finite_comapProjPointN_preimage_singleton 14
      (transcendental_xCoord_nsmul_of_isAlgClosed (W := y2AddYEqX3 AlgClosedQ) exampleFibreTwo
        (by norm_num)) q).toFinset.card ≤ 14 ^ 2 :=
  card_fibre_comapProjPointN_le_sq_of_ne_zero exampleFibreTwo exampleFibreFourteen _ q

/-- ⚠️ The **int**-cast form, which is what every `#1540` item 2 statement takes;
`exampleFibreFourteen` above is the nat-cast form and the two are not the same term. -/
private lemma exampleFibreFourteenInt : (((14 : ℕ) : ℤ) : AlgClosedQ) ≠ 0 := by
  push_cast; norm_num

/-- The non-constancy input at `n = 14`, **produced** from the index condition alone —
`transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`
(`EllipticCurves.FunctionField.MulByNXCoordFormula`), not the `3`-smooth ladder, which cannot
state anything at this index. -/
private theorem exampleFibreFourteenT :
    Transcendental AlgClosedQ
      ((14 • genericPoint (W := y2AddYEqX3 AlgClosedQ)).xCoord) :=
  transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero exampleFibreTwo
    exampleFibreFourteenInt

/-- **The contraction at `n = 14`, committed** — `#1540` item 2 at an index that is **even and not
`3`-smooth**, so it is reachable by `comapProjPointN_projPointOfPoint_of_smooth` at no hypotheses
whatsoever and by no odd-`n` statement anywhere.  ⚠️ `n = 12` above is `3`-smooth and a certificate
there is consistent with this layer proving nothing new. -/
example (P : (y2AddYEqX3 AlgClosedQ).Point) :
    comapProjPointN 14 exampleFibreFourteenT (projPointOfPoint (y2AddYEqX3 AlgClosedQ) P)
      = projPointOfPoint (y2AddYEqX3 AlgClosedQ) ((14 : ℕ) • P) :=
  comapProjPointN_projPointOfPoint_of_ne_zero exampleFibreTwo exampleFibreFourteenInt _ P

/-- **`#{p ↦ S} = 196` at `n = 14`, committed** — the fibre *equality*, which the `n = 14`
certificate above this section could only state as an inequality before `#1540` item 2. -/
example (S : (y2AddYEqX3 AlgClosedQ).Point) :
    (finite_comapProjPointN_preimage_singleton 14 exampleFibreFourteenT
      (projPointOfPoint (y2AddYEqX3 AlgClosedQ) S)).toFinset.card = 196 := by
  have h := card_fibre_comapProjPointN_projPointOfPoint_of_ne_zero
    (W := y2AddYEqX3 AlgClosedQ) exampleFibreTwo (n := 14) exampleFibreFourteenInt
    exampleFibreFourteenT S
  norm_num at h
  exact h

/-- **Every place over a rational point is unramified at `n = 14`, committed.** -/
example {p : ProjPoint (y2AddYEqX3 AlgClosedQ)} {S : (y2AddYEqX3 AlgClosedQ).Point}
    (hp : comapProjPointN 14 exampleFibreFourteenT p
      = projPointOfPoint (y2AddYEqX3 AlgClosedQ) S) :
    ramificationIdxN 14 exampleFibreFourteenT p = 1 :=
  ramificationIdxN_eq_one_of_comapProjPointN_eq_projPointOfPoint_of_ne_zero exampleFibreTwo
    exampleFibreFourteenInt _ hp

/-- **`[14]∗(S) = ∑_{p ↦ S} (p)` on `y² + y = x³`, committed** — the divisor identity `#418`'s
`hprin` consumes, at an index outside `{2, 3}`. -/
example (S : (y2AddYEqX3 AlgClosedQ).Point) :
    pullbackDivisorN 14 exampleFibreFourteenT
        (Finsupp.single (projPointOfPoint (y2AddYEqX3 AlgClosedQ) S) (1 : ℤ))
      = ∑ p ∈ (finite_comapProjPointN_preimage_singleton 14 exampleFibreFourteenT
          (projPointOfPoint (y2AddYEqX3 AlgClosedQ) S)).toFinset, Finsupp.single p (1 : ℤ) :=
  pullbackDivisorN_single_projPointOfPoint_of_ne_zero exampleFibreTwo exampleFibreFourteenInt _ S

end Nonvacuity

end IsAlgClosed

end CoordinateRing

end WeierstrassCurve.Affine
