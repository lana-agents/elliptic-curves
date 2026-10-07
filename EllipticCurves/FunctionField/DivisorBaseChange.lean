/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.CountValuationBridge
import EllipticCurves.FunctionField.FunctionFieldBaseChange
import EllipticCurves.FunctionField.CoordinateRingNormalGeneral
import EllipticCurves.FunctionField.PointClosedPoint
import EllipticCurves.Fixtures
import Mathlib.NumberTheory.RamificationInertia.Valuation

/-!
# Divisors under base change of the function field

`EllipticCurves.FunctionField.FunctionFieldBaseChange` builds `functionFieldMap W K : F(W) → K(W⁄K)`
and transports the three ring endomorphisms of `F(W)` along it.  That is the **endomorphism** half
of the base-change layer.  This file is the **divisor** half: it says what `functionFieldMap` does
to `ord` and to `divisor`.

## Why this is a different argument and not six more lemmas in the same style

`FunctionFieldBaseChange`'s own module block says `map_map_functionFieldMap` is *"what makes every
coordinate formula transportable"*, and every transport there is one.  ⚠️ **`ord` is not a
coordinate formula**: it is read off the factorisation of a principal fractional ideal, so
transporting it means knowing what `functionFieldMap` does to the **closed points** of `F(W)`.  That
file's `## Remaining work` says the same thing about itself, in terms — the divisor compatibilities
*"need the behaviour of `functionFieldMap` on the places of `F(W)`, which is a genuinely different
argument"* — and no **statement** in it mentions a place, an order of vanishing or a divisor.

`EllipticCurves.FunctionField.DivisorTransport` transports `ord` along a ring **isomorphism**
through `HeightOneSpectrum.mapEquiv`.  `functionFieldMap` is injective but not surjective, so that
route is closed too, and the transported order is not equal to the original: it is multiplied by a
ramification index.

## The mechanism

The two bricks were both already in the tree and had never been put together.

* Mathlib's `IsDedekindDomain.HeightOneSpectrum.valuation_liesOver` multiplies adic **valuations**
  by the ramification index along an extension of Dedekind domains:
  `v.valuation K x ^ e = w.valuation L (algebraMap K L x)` whenever `w` lies over `v`.
* `EllipticCurves.FunctionField.CountValuationBridge` converts between that `ℤᵐ⁰`-valued encoding
  and the `FractionalIdeal.count` encoding the divisor calculus uses.

Composing them gives `count_spanSingleton_algebraMap_liesOver`, and instantiating **that** at
`F[W] → K[W⁄K]` gives `ord_functionFieldMap`.  ⚠️ **The whole content of the file is the
instantiation**: the general lemma's proof is four lines and takes no curve.

## ⚠️ The instance layer is the work, and it is deliberately not global

`valuation_liesOver` wants `[Algebra K L]` and `[IsScalarTower A K L]` on the *fraction fields*.
`FunctionFieldBaseChange`'s `## Design notes` decides against exactly that, in terms: *"No
`Algebra F(W) K(W⁄K)` instance is registered: `functionFieldMap` is a bare `→+*` … This keeps the
file free of instance diamonds on `FunctionField`, which carries several algebra structures
already"*.  ⚠️ **That ruling is not merely quoted here, it is paid**: `algebraFunctionFieldMap` is
a `local instance` of this file, and no statement below mentions it.  Where `functionFieldMap` is
what a statement is about it is written out rather than hidden behind an `algebraMap`.  The two
towers it needs are proved once, as `isScalarTower_coordinateRing_baseChange` and
`isScalarTower_functionFieldMap`, and are supplied by hand at each use.

⚠️ **That claim is about ELABORATED types, and the source text cannot decide it.**
`IsScalarTower R S T` takes the `SMul S T` as an **argument**, so a tower stated against the local
instance carries `algebraFunctionFieldMap` inside its own type while its source mentions no algebra
at all.  A public theorem of that shape compiles, lints and is then unusable: `SMul F(W) K(W⁄K)` is
not synthesisable outside this file, so a consumer cannot so much as state the conclusion.
`isScalarTower_functionFieldMap` therefore takes the algebra as a **binder** and its map as a
hypothesis, and is applied here as `isScalarTower_functionFieldMap W K rfl`, while
`isScalarTower_coordinateRing_baseChange` needs no such treatment because both of its algebras are
global.  ⚠️ **None of this is visible to `grep`, to `lake build` or to `lake lint`** — only to
`Expr.getUsedConstants` on the elaborated type, which is how *"no statement below mentions it"* is
checked, over all **22** public declarations at once.  ⚠️ **That `22` is a count taken outside
this module block, and a line-anchored key gets it right only by cancelling one error against
another**: `^(private )?(noncomputable )?(theorem|lemma|def|abbrev|instance)`, with the `private`
rows dropped, returns **21** outside the block and misses `algebraFunctionFieldMap`, whose `def`
opens `@[reducible] noncomputable def`; run over the whole file it returns **22**, the extra being
a wrapped docstring line of this very section whose text begins with the word `instance`.  ⚠️ **The
false positive (+1) and the miss (−1) cancel**, so the scope and both members are named rather than
the total alone.  `## ⚠️ Two recogniser blind spots, and this file supplies a specimen of each`
takes that mode tree-wide and names this clause as its specimen.

## Main definitions

* `WeierstrassCurve.Affine.CoordinateRing.algebraFunctionFieldMap` : the `F(W)`-algebra structure on
  `K(W⁄K)` given by `functionFieldMap`, a **local** instance of this file only.

## Main statements

**The four hypothesis classes the statement bullets omit**, written out per declaration over all
**22** public declarations of this file.  ⚠️ It is a complete account of those four and not of
every binder: `count_spanSingleton_algebraMap_liesOver` alone carries sixteen instance binders,
being Mathlib's `AKLB` variable block copied verbatim.  ⚠️ **Re-scored over all 22 rather than
incremented** when the fibre section was added, and the re-score **reproduces the increment at all
four rows** (`+5`, `+5`, `+0`, `+3`): every figure moves by exactly the number of new declarations
its own list names, which is the check passing rather than a formality.  ⚠️ **22 is the count of
declarations with source text.**  Enumerating `Environment.const2ModIdx` for this module returns
**39** constants and **23** non-internal, non-blacklisted names; the twenty-third is
`IsDedekindDomain.HeightOneSpectrum.under.congr_simp`, a congruence lemma Lean generates and no
line of this file writes.

* `[W.IsElliptic]`: carried by **15** — `ord_functionFieldMap`,
  `ramificationIdx'_functionFieldMap_ne_zero`, `ramificationIdx'_functionFieldMap_pos`,
  `divisor_functionFieldMap`, `ord_functionFieldMap_eq_zero_iff`, `dvd_ord_functionFieldMap`,
  `ord_functionFieldMap_under`, `divisor_functionFieldMap_under`,
  `ord_functionFieldMap_under_eq_zero_iff`, `dvd_ord_functionFieldMap_under`, `exists_liesOver`,
  `exists_under_eq`, `ord_eq_of_forall_ord_functionFieldMap_eq`,
  `divisor_eq_of_divisor_functionFieldMap_eq` and `divisor_functionFieldMap_eq_zero_iff`.  It is
  where `[IsDedekindDomain W.CoordinateRing]` comes from.  ⚠️ The other **7** do **not** carry it,
  and the three easily missed are the instances: `count_spanSingleton_algebraMap_liesOver` (no curve
  at all), `algebraFunctionFieldMap`, `isScalarTower_coordinateRing_baseChange`,
  `isScalarTower_functionFieldMap`, **`instModuleFiniteCoordinateRingMap`**,
  **`instIsIntegralCoordinateRingMap`** and **`instFaithfulSMulCoordinateRingMap`**.
* `[Module.Finite F K]`: carried by **11** — `instModuleFiniteCoordinateRingMap` and
  `instIsIntegralCoordinateRingMap`; the four `under`-forms `ord_functionFieldMap_under`,
  `divisor_functionFieldMap_under`, `ord_functionFieldMap_under_eq_zero_iff` and
  `dvd_ord_functionFieldMap_under`, which get it through `instIsIntegralCoordinateRingMap`; and the
  five of the fibre section, `exists_liesOver`, `exists_under_eq`,
  `ord_eq_of_forall_ord_functionFieldMap_eq`, `divisor_eq_of_divisor_functionFieldMap_eq` and
  `divisor_functionFieldMap_eq_zero_iff`, which get it through the same instance.
  ⚠️ `instFaithfulSMulCoordinateRingMap` does **not** take it — injectivity of
  `CoordinateRing.map` holds for any field extension.
* `[w.asIdeal.LiesOver v.asIdeal]`: **bound** by **7** — `count_spanSingleton_algebraMap_liesOver`
  in the abstract setting, and the six curve statements that both name a `v` **and** bind it.
  ⚠️ *Naming a `v` is not the key*: **nine** curve statements below name one, the other three being
  `exists_liesOver`, `exists_under_eq` and `ord_eq_of_forall_ord_functionFieldMap_eq`, which produce
  a `w` over `v` rather than assuming one.  ⚠️ The four `under`-forms carry **no** `LiesOver`
  hypothesis: `Ideal.over_under` discharges it by construction, which is the whole point of taking
  `[Module.Finite F K]` instead.  ⚠️ **This is the one figure of the four that a
  `getUsedConstants` key does not reproduce**: it returns **8**, because `exists_liesOver` has
  `Ideal.LiesOver` in its *conclusion*.  Bound as a hypothesis: 7.  Occurring in the type: 8.
* `f ≠ 0` (`x ≠ 0` in the abstract statement): carried by **12** declarations and **14** binders —
  every statement that mentions `ord` or `divisor` of an `f`, i.e. all **15** of the
  `[W.IsElliptic]` group except the two `ramificationIdx'` statements and the two existence
  statements `exists_liesOver` and `exists_under_eq`, plus
  `count_spanSingleton_algebraMap_liesOver`.  ⚠️ The declaration and binder counts differ because
  `ord_eq_of_forall_ord_functionFieldMap_eq` and `divisor_eq_of_divisor_functionFieldMap_eq` each
  bind **two** — they compare two functions.

* `IsDedekindDomain.HeightOneSpectrum.count_spanSingleton_algebraMap_liesOver` : the general
  Dedekind-domain statement.  **No curve is mentioned and it is upstreamable as it stands.**
* `WeierstrassCurve.Affine.CoordinateRing.ord_functionFieldMap` :
  `ord w (functionFieldMap f) = e * ord v f` for `w` lying over `v`.
* `WeierstrassCurve.Affine.CoordinateRing.ramificationIdx'_functionFieldMap_ne_zero` and
  `..._pos` : the factor is **not** zero, so the transport loses no information.
* `WeierstrassCurve.Affine.CoordinateRing.divisor_functionFieldMap` : the same, read on `divisor`.
* `WeierstrassCurve.Affine.CoordinateRing.ord_functionFieldMap_eq_zero_iff` : `ord v f = 0` iff
  `ord w (functionFieldMap f) = 0`, for **the** `w` the statement is given.  ⚠️ It is not quantified
  over the fibre **in its conclusion**, and **no statement below carries a universal over one fibre
  there** — that is the key, and under it the clause is as true as it was at `2d7f0e0`.
  `exists_liesOver` and `exists_under_eq` are the only two whose conclusion quantifies over a fibre
  at all, and both do it *existentially*.  ⚠️ **Under the binder key the answer is different**: a
  `∀ v w, [w.asIdeal.LiesOver v.asIdeal] → …` **is** a universal over each fibre, and this bullet's
  own subject is one of the **7** statements below carrying that binder, against **5** more that
  name `HeightOneSpectrum.under` — so **twelve** mention a fibre, scored over the public signatures
  here with each split at `:=` so that no proof contributes.  That `7` is the figure
  `## Main statements` publishes above: the two keys agree on the total and differ by one member in
  each direction, a signature scan taking `exists_liesOver` from its conclusion and missing
  `count_spanSingleton_algebraMap_liesOver`, which inherits `LiesOver` from Mathlib's `AKLB`
  `variable` block.  **Say which scope a re-run covers.**
  ⚠️ **The fibre-quantified `iff` costs nothing, and it is this statement's own binder**: read at a
  fixed `v` and at every `w` over it, `ord_functionFieldMap_eq_zero_iff` **is**
  `∀ w over v, (ord w (functionFieldMap f) = 0 ↔ ord v f = 0)` — no new lemma, no new hypothesis and
  no finiteness, for any `K / F`.  The two forms that *state* it rather than derive it,
  `ord_functionFieldMap_under_eq_zero_iff` over `w` alone and
  `divisor_functionFieldMap_eq_zero_iff` over both spectra, are `[Module.Finite F K]` forms, so at
  `K = F̄` the derivation above is the one that still runs — which is what `## What is *not* here`
  says of the `under`-forms.
* `WeierstrassCurve.Affine.CoordinateRing.dvd_ord_functionFieldMap` : `n ∣ ord v f` implies
  `n ∣ ord w (functionFieldMap f)` — the shape a descent argument takes as a hypothesis.
* `WeierstrassCurve.Affine.CoordinateRing.instModuleFiniteCoordinateRingMap` and
  `instIsIntegralCoordinateRingMap` : for a **finite** extension `K / F`, `K[W⁄K]` is a finite and
  hence integral `F[W]`-module, which is what makes `HeightOneSpectrum.under` total.
* `WeierstrassCurve.Affine.CoordinateRing.ord_functionFieldMap_under` and
  `divisor_functionFieldMap_under` : the `v`-free forms, quantified over `w` alone.
* `WeierstrassCurve.Affine.CoordinateRing.instFaithfulSMulCoordinateRingMap` : `F[W] → K[W⁄K]` is
  faithful, being injective.  **No finiteness**; it is what the going-up lemma below takes.
* `WeierstrassCurve.Affine.CoordinateRing.exists_liesOver` and `exists_under_eq` : **the fibre over
  a closed point of `F(W)` is non-empty**, i.e. `HeightOneSpectrum.under` is surjective.
* `WeierstrassCurve.Affine.CoordinateRing.ord_eq_of_forall_ord_functionFieldMap_eq` and
  `divisor_eq_of_divisor_functionFieldMap_eq` : **the descent.**  `n • divisor g = divisor f` proved
  over a finite `K / F` holds over `F`.  ⚠️ It consumes no value for the ramification index — the
  same `e` stands in front of both sides and cancels.
* `WeierstrassCurve.Affine.CoordinateRing.divisor_functionFieldMap_eq_zero_iff` : `divisor f = 0`
  iff `divisor (functionFieldMap f) = 0`, over **both** spectra rather than at one named pair.

## What is *not* here

* **An infinite extension.**  `instIsIntegralCoordinateRingMap` is proved from `[Module.Finite F K]`
  through `baseChangeLinearEquiv`, so the `under`-forms cover finite `K / F` only.  For `K = F̄` the
  statement is true — integrality is a colimit of the finite case — and **nothing below proves it**;
  the `LiesOver`-forms, which carry no finiteness, do apply there once a `(v, w)` pair is in hand.
* **A formula for the ramification index.**  `ramificationIdx'` is left abstract.  In particular
  ⚠️ **nothing below says it is `1`**, which is what a separable `K / F` would give, and which is
  what a consumer wanting `divisor` to transport *on the nose* needs.  The positivity statements
  are all that is proved about it.  ⚠️ **A consumer comparing two divisors does not need it**, and
  since the fibre section landed this file contains such a consumer:
  `divisor_eq_of_divisor_functionFieldMap_eq` puts the same `e` in front of both sides and cancels
  it.  The absence above is a limit on transporting *one* divisor, not on relating two.
* **`divisorProj`.**  Only the affine `divisor` transports here.  The point at infinity is not a
  height-one prime of `F[W]` and `ordInfty` is a different object.  Below the module block the
  tokens `divisorProj`, `ProjPoint` and `ordInfty` do not occur.
* **The `Point.map` bridge.**  `#692`'s item 3 asks for the base-changed torsion point to be the
  image of the original.  That is about `Point`, not about `divisor`, and is untouched: no statement
  below has a `W.Point` in it.  ⚠️ The one point-shaped thing here is `pointClosedPoint`, in the
  `Nonvacuity` section, and it takes a `W.Equation` rather than a `Point`.
* **Any discharge of `hprin`.**  `#962` stays a gate record.  Below the module block the tokens
  `exists_gS_two` and `NthRootOfPullback` do not occur, and no statement is about a principal
  divisor.  ⚠️ The word *principal* does occur once below, in
  `count_spanSingleton_algebraMap_liesOver`'s docstring, about a principal **fractional ideal** —
  which is what `count` is defined on, and is not a divisor claim.
* ~~**Surjectivity of `w ↦ under w`.**~~  ⚠️ **Retired.**  This bullet used to read *"That every
  closed point of `F(W)` has a point of `K(W⁄K)` above it is
  `Ideal.exists_maximal_ideal_liesOver_of_isIntegral`'s business and is not stated below;
  `ord_functionFieldMap_eq_zero_iff` is therefore an `iff` at one named `w` and **not** over the
  fibre."*  Both halves are now discharged **in this file**: `exists_under_eq` is the surjectivity,
  and `divisor_functionFieldMap_eq_zero_iff` is the `iff` over the whole spectrum.  The prediction
  about which Mathlib lemma does it was right — it is that lemma, at
  `instIsIntegralCoordinateRingMap` and `instFaithfulSMulCoordinateRingMap`, plus a `ne_bot` step
  the lemma does not supply.  `ord_functionFieldMap_eq_zero_iff` itself is unchanged and is still
  stated at one named pair; what is new is the quantified consequence beside it.

## Non-vacuity

The `Nonvacuity` section instantiates `ord_functionFieldMap_under` with **no hypothesis at all** on
`EllipticCurves.Fixture.y2EqX3SubX` over `ℚ`, base-changed to `(X ^ 2 + 1 : ℚ[X]).SplittingField`,
at the closed point of the rational point `(0, 0)` and at the function `x`.

* ⚠️ **The extension is proper** — `certRoot_not_mem_range` — so nothing certified there is a
  statement about an isomorphism in disguise.  A base change along an isomorphism would leave every
  ramification index `1` and make the whole file trivially true.
* `[Module.Finite ℚ _]` is Mathlib's global `FiniteDimensional K f.SplittingField`, found by
  typeclass search.  ⚠️ `IsSplittingField ℚ _ (X ^ 2 + 1)` is **not** found by typeclass search at
  this pin — `Polynomial.IsSplittingField.splittingField` discharges it when applied by hand and
  `inferInstance` fails, even with the instance attribute set locally — so `certRoot` is built from
  `Polynomial.SplittingField.splits` instead.  The same trap is recorded on `certRoot`'s docstring.
* ⚠️ **It certifies that the hypothesis class is inhabited and that
  `HeightOneSpectrum (K[W⁄K])` is not empty; it does not evaluate either side of the equation.**
  Evaluating `ord` at a `pointClosedPoint` goes through
  `EllipticCurves.FunctionField.DivisorTheoryElliptic`'s torsion machinery, which this file does
  not import, so the instance is certified as a statement and not as an arithmetic.
* The fibre section is certified at the **same** curve and the **same** proper extension:
  `exists_under_eq_cert` produces a closed point of `K[W⁄K]` above the closed point of `(0, 0)` on
  the **base** curve.  ⚠️ That is the certificate that has to be over a proper extension: along an
  isomorphism `under` is a bijection and surjectivity is free, so a certificate over `F̄` or over
  `F` itself would certify nothing.  ⚠️ **The two certificate points are different objects over
  different rings** — `certPoint` is a `HeightOneSpectrum` of `K[W⁄K]` and `certPointBase` one of
  `ℚ[W]` — and it is the second that this section needed and did not have.

## ⚠️ Two recogniser blind spots, and this file supplies a specimen of each

`#2199`, out of `#2184`'s pointer sweep.  Both seeds are published with their recogniser, their
corpus and their sha so that a re-runner reproduces them rather than re-invents one (`README.md`
`### Reach clauses`, `#2087`), and ⚠️ **nothing anywhere is repaired on the strength of this
section**: a population is measured before it is swept.

⚠️ **EVERY COORDINATE BELOW IS AT `0b8f3d1`, NOT AT THIS HEAD.**  This section is itself an
insertion into the module block it censuses: it moves every line of this file below `:72` and it
adds directional words of its own, so both of its figures are published as **deltas** and neither
is an endpoint pair (`README.md` `### The neighbour population`).  ⚠️ **A census of a file,
published inside that file, cannot be keyed on this head without going stale on the next edit —
which is `#2037`'s axis, turned on this paragraph.**  Read the coordinates with
`git show 0b8f3d1:EllipticCurves/FunctionField/DivisorBaseChange.lean`.

⚠️⚠️ **THE BASE MOVED UNDER THIS SECTION BETWEEN TWO ROUNDS, AND IT MOVED ONE OF ITS TWO CENSUSES
AND NOT THE OTHER — WHICH IS THE WHOLE DIFFERENCE BETWEEN A REF AND A PREDICTION.**  Round 1 keyed
every coordinate here to `5dba859`; `0b8f3d1` landed at 2026-09-27T01:29:48Z.  This file's blob is
`34a6b2c100a5adde9e12a819fe13c8d937e86c78` at **both**, so the module-block census below is unmoved
across the base change and all sixteen of its line numbers still resolve.  ⚠️ **The tree-wide
census is not**: `0b8f3d1` is PR #813, which repaired `XDifference`:70 — **the one row this seed
convicted** — so that population reads `77 in 45` at `5dba859` and **`76 in 44`** here, and the row
is discharged.  ⚠️ **A delta's FIRST endpoint is a fact about a ref; its SECOND is a prediction
about a tree nobody has built, and a LANDING turns the second into the first with no edit to either
branch.**  Round 1 published the second endpoint of the tree-wide delta as `82 in 45`; the landing
falsified both of its numbers before anyone could re-run it, and the figure below is a fact about
`0b8f3d1` and this commit rather than a prediction about an order of landings.

### 1. A pointer keyed on a definite noun phrase is a third shape

`\b(above|below|earlier|later|preceding|following)\b` inside this module block, `:13`–`:245`,
returns **16** occurrences on **16** lines at `0b8f3d1`, in **six** shapes:

     2  mathematical `above`, one place lying over another       `:204` `:234`
    10  directional over a named region, subject named           `:57` `:116` `:140` `:145` `:168`
                                                                 `:182` `:185` `:196` `:200` `:205`
     1  text pointer keyed on a NAME                             `:148`
     2  text pointer keyed on a DEFINITE NOUN PHRASE             `:158` `:190`
     1  the seed matching inside a MARKED QUOTATION              `:71`
     0  text pointer keyed on a COORDINATE                       discharged by PR #808

⚠️ **Published as a delta, because this section is inside the block it counts**: the six-way census
is `0b8f3d1`'s, and this commit adds **25** occurrences on **18** lines here and
**0** in the `22` repair, so the same seed over the same block returns **41** on
**34** once this lands.  ⚠️ **No landing order changes THAT — and the clause is scoped to
this census and to this file**, which no other open pull request touches, measured and not assumed.
It says nothing about the tree-wide figures below, where landing order is exactly what moved them.

⚠️ **The figure published for this census is `17` at four shapes, and that is the count at
`c6ef24a` — the PARENT.**  PR #808's own repair of `:153` deleted the word *above* from that line,
so the census in its message is one its own head already falsified (`#1972`).  ⚠️ **And `:71`
is a shape the same commit created**: the repair there put a marked quotation of `:57` on the line,
and the seed now scores the quoted *below* — not a pointer of that sentence at all.

`:158` (*"the derivation above"*) and `:190` (*"The absence above"*) are sound, and the reason is a
SCOPE and not a name: each points inside its own bullet — `:158` to the derivation at `:152`–`:155`
and `:190` to the clause at `:185` — so the referent travels with the pointer under any insertion
outside that bullet.  ⚠️ **A second derivation, or a second absence, inserted INTO either bullet
makes it ambiguous with no edit to either file**, which is `#2184`'s criterion rather than
`#2037`'s.  A name cannot fail that way and a coordinate fails louder.

**Tree-wide the shape is a register and not a defect.**  Whitespace-normalised, over the **435**
tracked `.lean` files and `README.md` at `0b8f3d1`:

    \b[Tt]he (claim|absence|derivation|argument|ruling|bullet|sentence|paragraph|list|table)
    (above|below)\b

returns **76** occurrences in **44** files — *paragraph* 27, *sentence* 23, *argument* 8, *bullet*
6, *list* 3, *ruling* 3, *claim* 2, *table* 2, *derivation* 1, *absence* 1 — and **58** *above*
against **18** *below*.  ⚠️ **A per-line grep returns 64 of the 76; twelve WRAP** (`#2190`).
**74** of the **76** carry eight or more words of their own unit before the pointer, so the
referent can sit inside it.  ⚠️ **Two open their unit and must point outside it, and both are
sound, by two different routes:**

* `README.md:917` — *"the reason the paragraph above already gives about
  `exists_gS_n_weilPairingElt_ne_one`"*: the pointer phrase carries a NAME, so it is sound the way
  a name is.  It is also the repair a scope-less pointer wants.
* `EllipticCurves.FunctionField.PullbackDivisor`:42 — *"The argument below"* opens a paragraph and
  points forward inside its own `##` section.

⚠️ **The third member of that bucket was the one row this seed convicted, and it is DISCHARGED at
this base.**  At `5dba859` the seed returned **77** in **45** with the split **74 / 3**, and the
third was `EllipticCurves.Torsion.XDifference`:70, whose first prose line after the `##` at `:68`
read *"The derivation above is three lines of `ring` on top of the `r = 1` relation"* — keyed to
`5dba8596d1dadfb67e82578f5c85d71469836f6d:EllipticCurves/Torsion/XDifference.lean:70`, because
those words are absent from `0b8f3d1` and from every tree after it and that ref is the only
spelling a later reader can reach them at.  Its referent was the derivation at `:17`–`:34`, in the
H1 body two `##` sections above, and neither paragraph immediately before `:68` contains one.  It
was filed as `#2208` rather than folded into whoever opened that file next — `#2184` exists to say
that a note with no addressee is nobody's job — and ⚠️ **PR #813 landed that repair, which is the
whole reason the population above is one smaller than round 1's.**

⚠️ **So the shape needs no sweep and no `README.md` rule: 74 of the 76 are sound by scope, the
remaining two by a name and by a direction, and the one row that failed was filed and repaired in
the time this branch took to write two rounds.  What the shape needs is the scope condition stated
once, which this subsection is.**

⚠️ **A delta again, and in THREE rows rather than two, because this commit's additions do not
belong in either existing bucket**: it adds **5** occurrences on **4** lines to
that seed, so the tree returns **81** in **44** once this lands.  ⚠️ **Every one of
them sits inside a marked quotation of a row this section reports, and a quoted pointer points
nowhere** — so the mechanical *eight words of its own unit* key drops them in the second bucket
while that bucket's stated predicate, *must point outside it*, is false of every one of them.  They
are counted as their own row instead of absorbed:

    74          carry >= 8 words of their unit before the pointer   unmoved by this commit
     2          open their unit and point outside it                unmoved by this commit
     5          inside a marked quotation, pointing nowhere         ⚠️ all of this commit's

**That is the shape `#2206` is about, met while measuring something else — and it is the same
correction this subsection makes to PR #808 at the file level, now made to itself at the tree
level.**

### 2. A line-anchored declaration key matches docstring prose

Every module docstring in this development wraps at 100 codepoints, so any `^`-anchored declaration
recogniser can land on a prose line that merely begins with a Lean keyword.  Scored as prose when
the line lies inside a `/- … -/` block, over the **435** tracked `.lean` files at `0b8f3d1`:

    ^(private |protected |noncomputable |@\[[^\]]*\] )*
     (theorem|lemma|def|abbrev|instance|structure|class|example)\b

returns **6044** hits, of which ⚠️ **131 in 98 of the 435 files are not declarations of their
file** — **122** wrapped prose on a keyword, in **93** files, and **9** a signature or a code sample
printed inside a docstring.  By keyword: `instance` **58**, `theorem` **42**, `structure` **13**,
`class` **10**, `lemma` **6**, `example` **1**, `def` **1**.  At `0b8f3d1` this file carries
exactly one of the 122 — the wrapped `instance` line under
`## ⚠️ The instance layer is the work, and it is deliberately not global`, which is the false
positive that section's own `22` clause names.  ⚠️ **The heading is given in full because this
file carries a second one reading `## The instance layer`, outside the module block**, and a
prefix would key on neither.  ⚠️ **Every cell of this census is identical at `5dba859` and at
`0b8f3d1`** — the 6044, the 131, the 98, the keyword split and this file's one member at `:64` —
which is what a census keyed on a corpus rather than on one blob does when the base moves under it.

⚠️ **This subsection adds none of the 131, and that is a check rather than an assumption**: a
draft of it did add one — a wrapped line whose text began with the word `instance` — and the seed
is what found it.  It was re-wrapped and the seed re-run until the tree returned the base figure.
**The mode is a property of prose wrapped at a fixed width, so nothing here is safe from it by
being about it.**

⚠️ **The general form, and it reaches past declarations: a recogniser whose blind spots cancel
is indistinguishable from a correct one at the total.**  That `22` clause is the clean instance: a
re-runner who applies the key to the whole file gets the true **22** and concludes the key needs no
scope, which is the opposite of what the clause says.  The only test that separates the two is
**printing the membership**, which `README.md` `### Reach clauses` already asks of a population
claim (`#1668`).  ⚠️ **`main` publishes a `^`-anchored declaration key in 10 of its 759 commit
messages and `README.md` publishes one 0 times** — where *a key* is read as
`` \^[^\n]{0,120}?\b(theorem|lemma|def|abbrev|instance|structure|class|example)\b ``, printed
because the count is a function of it: the same corpus returns **4** if the key must lie inside one
backticked span and **2** if the caret must be followed immediately by the keyword or by a group
opening it, and a fourth reading returned the **6** this clause published in round 1 with no
recogniser beside it.  ⚠️ **The `0` is 0 under every reading tried**, so the direction of the claim
survives the spread and the absolute does not — which is the point: every such count on this board
was taken against a recogniser its reader cannot reconstruct (`#2087`).

## References

Silverman, *The Arithmetic of Elliptic Curves*, II.3 (divisors) and II.2 (maps of curves and
ramification).
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal WithZero
open scoped nonZeroDivisors TensorProduct

namespace IsDedekindDomain.HeightOneSpectrum

variable {A K : Type*} (L : Type*) {B : Type*}
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]
variable [Field K] [Field L] [Algebra K L]
variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]
variable (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

/-- **The `count` of a principal fractional ideal multiplies by the ramification index.**

This is `IsDedekindDomain.HeightOneSpectrum.valuation_liesOver` read through the `count` ↔
valuation bridge of `EllipticCurves.FunctionField.CountValuationBridge`: valuations multiply by
`e` in `ℤᵐ⁰`, and `count` is `−log` of the valuation, so counts multiply by `e` in `ℤ`.

⚠️ No curve is mentioned and no finiteness is assumed — `w` lying over `v` is the only relation
between the two primes. -/
theorem count_spanSingleton_algebraMap_liesOver {x : K} (hx : x ≠ 0) :
    count L w (spanSingleton B⁰ (algebraMap K L x))
      = (v.asIdeal.ramificationIdx' w.asIdeal : ℤ) * count K v (spanSingleton A⁰ x) := by
  have hx' : algebraMap K L x ≠ 0 := by simpa using (algebraMap K L).injective.ne hx
  rw [count_eq_neg_log_valuation w hx', ← valuation_liesOver L v w x,
    valuation_eq_exp_neg_count v hx, ← exp_nsmul, log_exp]
  ring

end IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine.CoordinateRing

variable {F : Type*} [Field F] (W : Affine F) (K : Type*) [Field K] [Algebra F K]

/-! ## The instance layer -/

/-- The `F(W)`-algebra structure on `K(W⁄K)` whose `algebraMap` is `functionFieldMap W K`.

⚠️ **A `local instance` of this file and nothing more.**  PR #356 deliberately left
`functionFieldMap` a bare `→+*`; registering this globally is what that decision refused, and no
statement in this file mentions it — checked on the elaborated types rather than on the source
text, `IsScalarTower` being exactly the shape that carries such an instance into a statement which
never names it. -/
@[reducible] noncomputable def algebraFunctionFieldMap :
    Algebra W.FunctionField (W.map (algebraMap F K)).FunctionField :=
  (functionFieldMap W K).toAlgebra

attribute [local instance] algebraFunctionFieldMap

/-- `F[W] → K[W⁄K] → K(W⁄K)` is the structural map `F[W] → K(W⁄K)`. -/
theorem isScalarTower_coordinateRing_baseChange :
    IsScalarTower W.CoordinateRing (W.map (algebraMap F K)).CoordinateRing
      (W.map (algebraMap F K)).FunctionField :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- `F[W] → F(W) → K(W⁄K)` is the structural map `F[W] → K(W⁄K)`.  This is
`functionFieldMap_algebraMap` — the defining property of `functionFieldMap` — packaged as a tower,
and it is what lets `valuation_liesOver` see the base-change map at all.

⚠️ **The `F(W)`-algebra structure is a hypothesis here and not this file's `local instance`.**
`IsScalarTower R S T` takes the `SMul S T` as an argument, so a tower stated against
`algebraFunctionFieldMap` would carry that local instance inside its own elaborated type, and a
consumer of this file could not so much as state the conclusion.  Taking the algebra as a binder
and its map as a hypothesis keeps the statement usable downstream; inside this file it is applied
as `isScalarTower_functionFieldMap W K rfl`. -/
theorem isScalarTower_functionFieldMap
    [Algebra W.FunctionField (W.map (algebraMap F K)).FunctionField]
    (h : algebraMap W.FunctionField (W.map (algebraMap F K)).FunctionField
      = functionFieldMap W K) :
    IsScalarTower W.CoordinateRing W.FunctionField (W.map (algebraMap F K)).FunctionField :=
  IsScalarTower.of_algebraMap_eq fun a => by
    rw [h]; exact (functionFieldMap_algebraMap W K a).symm

/-- **For a finite extension `K / F`, `K[W⁄K]` is a finite `F[W]`-module.**  The `F[W]`-linear
isomorphism `K[W⁄K] ≃ₗ F[W] ⊗[F] K` is `baseChangeLinearEquiv`, built for faithful flatness in
`EllipticCurves.FunctionField.CoordinateRingBaseChange`; finiteness of a base change is then
Mathlib's `Module.Finite.base_change`. -/
noncomputable instance instModuleFiniteCoordinateRingMap [Module.Finite F K] :
    Module.Finite W.CoordinateRing (W.map (algebraMap F K)).CoordinateRing := by
  haveI : Module.Finite W.CoordinateRing (W.CoordinateRing ⊗[F] K) := inferInstance
  exact Module.Finite.equiv (baseChangeLinearEquiv W K).symm

/-- **For a finite extension `K / F`, `K[W⁄K]` is integral over `F[W]`.**  This is what makes
`IsDedekindDomain.HeightOneSpectrum.under` total, and hence what removes the `v` from the statements
below. -/
instance instIsIntegralCoordinateRingMap [Module.Finite F K] :
    Algebra.IsIntegral W.CoordinateRing (W.map (algebraMap F K)).CoordinateRing :=
  Algebra.IsIntegral.of_finite _ _

/-- **`F[W] → K[W⁄K]` is faithful**, because it is injective.

⚠️ Unlike the two instances above this needs **no** finiteness: `CoordinateRing.map` is injective
for any field extension `K / F` (`FunctionFieldBaseChange.map_algebraMap_injective`).  It is stated
because `Ideal.exists_maximal_ideal_liesOver_of_isIntegral` takes it as an instance argument
alongside integrality, and without it the going-up lemma does not apply to this algebra. -/
instance instFaithfulSMulCoordinateRingMap :
    FaithfulSMul W.CoordinateRing (W.map (algebraMap F K)).CoordinateRing :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (map_algebraMap_injective W K)

/-! ## The transport -/

variable [W.IsElliptic]

/-- **Orders of vanishing multiply by the ramification index under base change.**

For a closed point `w` of the base-changed curve lying over a closed point `v` of `W`, and a nonzero
`f ∈ F(W)`, the order of `functionFieldMap f` at `w` is `e(w | v)` times the order of `f` at `v`.

⚠️ The factor is genuinely there: `ramificationIdx'_functionFieldMap_ne_zero` says only that it is
nonzero, and **nothing in this file says it is `1`**. -/
theorem ord_functionFieldMap (v : HeightOneSpectrum W.CoordinateRing)
    (w : HeightOneSpectrum (W.map (algebraMap F K)).CoordinateRing)
    [w.asIdeal.LiesOver v.asIdeal] {f : W.FunctionField} (hf : f ≠ 0) :
    ord w (functionFieldMap W K f)
      = (v.asIdeal.ramificationIdx' w.asIdeal : ℤ) * ord v f := by
  haveI := isScalarTower_coordinateRing_baseChange W K
  haveI := isScalarTower_functionFieldMap W K rfl
  rw [ord, ord]
  exact count_spanSingleton_algebraMap_liesOver
    (A := W.CoordinateRing) (K := W.FunctionField)
    ((W.map (algebraMap F K)).FunctionField) v w hf

variable {W K}

/-- **The ramification index is nonzero**, so `ord_functionFieldMap` loses no information. -/
theorem ramificationIdx'_functionFieldMap_ne_zero (v : HeightOneSpectrum W.CoordinateRing)
    (w : HeightOneSpectrum (W.map (algebraMap F K)).CoordinateRing)
    [w.asIdeal.LiesOver v.asIdeal] : v.asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
  Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot

/-- **The ramification index is positive.** -/
theorem ramificationIdx'_functionFieldMap_pos (v : HeightOneSpectrum W.CoordinateRing)
    (w : HeightOneSpectrum (W.map (algebraMap F K)).CoordinateRing)
    [w.asIdeal.LiesOver v.asIdeal] : 0 < v.asIdeal.ramificationIdx' w.asIdeal :=
  Nat.pos_of_ne_zero (ramificationIdx'_functionFieldMap_ne_zero v w)

/-- **The divisor form of `ord_functionFieldMap`.** -/
theorem divisor_functionFieldMap (v : HeightOneSpectrum W.CoordinateRing)
    (w : HeightOneSpectrum (W.map (algebraMap F K)).CoordinateRing)
    [w.asIdeal.LiesOver v.asIdeal] {f : W.FunctionField} (hf : f ≠ 0) :
    divisor (W.map (algebraMap F K)) (functionFieldMap W K f) w
      = (v.asIdeal.ramificationIdx' w.asIdeal : ℤ) * divisor W f v := by
  simpa only [divisor_apply] using ord_functionFieldMap W K v w hf

/-- **`f` is a unit at `v` exactly when its base change is a unit at any `w` over `v`.**  The
ramification index is nonzero, so it cannot create or destroy a zero. -/
theorem ord_functionFieldMap_eq_zero_iff (v : HeightOneSpectrum W.CoordinateRing)
    (w : HeightOneSpectrum (W.map (algebraMap F K)).CoordinateRing)
    [w.asIdeal.LiesOver v.asIdeal] {f : W.FunctionField} (hf : f ≠ 0) :
    ord w (functionFieldMap W K f) = 0 ↔ ord v f = 0 := by
  rw [ord_functionFieldMap W K v w hf, mul_eq_zero]
  simp [ramificationIdx'_functionFieldMap_ne_zero v w]

/-- **Divisibility of orders is preserved.**  This is the shape a descent argument consumes: an
order that is `n`-divisible over `F` stays `n`-divisible over `K`. -/
theorem dvd_ord_functionFieldMap {n : ℤ} (v : HeightOneSpectrum W.CoordinateRing)
    (w : HeightOneSpectrum (W.map (algebraMap F K)).CoordinateRing)
    [w.asIdeal.LiesOver v.asIdeal] {f : W.FunctionField} (hf : f ≠ 0) (hd : n ∣ ord v f) :
    n ∣ ord w (functionFieldMap W K f) := by
  rw [ord_functionFieldMap W K v w hf]
  exact hd.mul_left _

/-! ## The `v`-free form, for a finite extension

`IsDedekindDomain.HeightOneSpectrum.under` sends a closed point of `K[W⁄K]` to the closed point of
`F[W]` it contracts to.  It needs integrality, which `instIsIntegralCoordinateRingMap` supplies for
a finite `K / F`, and `Ideal.over_under` then discharges the `LiesOver` hypothesis by construction.
-/

variable (W K)

/-- **The transport, quantified over `w` alone.**  Every closed point of the base-changed curve
contracts to one of `W`, and the order there is the original order times the ramification index. -/
theorem ord_functionFieldMap_under [Module.Finite F K]
    (w : HeightOneSpectrum (W.map (algebraMap F K)).CoordinateRing)
    {f : W.FunctionField} (hf : f ≠ 0) :
    ord w (functionFieldMap W K f)
      = ((HeightOneSpectrum.under W.CoordinateRing w).asIdeal.ramificationIdx' w.asIdeal : ℤ)
          * ord (HeightOneSpectrum.under W.CoordinateRing w) f := by
  haveI : w.asIdeal.LiesOver (HeightOneSpectrum.under W.CoordinateRing w).asIdeal := by
    rw [HeightOneSpectrum.under_asIdeal]; infer_instance
  exact ord_functionFieldMap W K _ w hf

/-- **The divisor form of `ord_functionFieldMap_under`.** -/
theorem divisor_functionFieldMap_under [Module.Finite F K]
    (w : HeightOneSpectrum (W.map (algebraMap F K)).CoordinateRing)
    {f : W.FunctionField} (hf : f ≠ 0) :
    divisor (W.map (algebraMap F K)) (functionFieldMap W K f) w
      = ((HeightOneSpectrum.under W.CoordinateRing w).asIdeal.ramificationIdx' w.asIdeal : ℤ)
          * divisor W f (HeightOneSpectrum.under W.CoordinateRing w) := by
  haveI : w.asIdeal.LiesOver (HeightOneSpectrum.under W.CoordinateRing w).asIdeal := by
    rw [HeightOneSpectrum.under_asIdeal]; infer_instance
  exact divisor_functionFieldMap _ w hf

/-- **The unit criterion, quantified over `w` alone.** -/
theorem ord_functionFieldMap_under_eq_zero_iff [Module.Finite F K]
    (w : HeightOneSpectrum (W.map (algebraMap F K)).CoordinateRing)
    {f : W.FunctionField} (hf : f ≠ 0) :
    ord w (functionFieldMap W K f) = 0 ↔
      ord (HeightOneSpectrum.under W.CoordinateRing w) f = 0 := by
  haveI : w.asIdeal.LiesOver (HeightOneSpectrum.under W.CoordinateRing w).asIdeal := by
    rw [HeightOneSpectrum.under_asIdeal]; infer_instance
  exact ord_functionFieldMap_eq_zero_iff _ w hf

/-- **Divisibility, quantified over `w` alone.** -/
theorem dvd_ord_functionFieldMap_under [Module.Finite F K] {n : ℤ}
    (w : HeightOneSpectrum (W.map (algebraMap F K)).CoordinateRing)
    {f : W.FunctionField} (hf : f ≠ 0)
    (hd : n ∣ ord (HeightOneSpectrum.under W.CoordinateRing w) f) :
    n ∣ ord w (functionFieldMap W K f) := by
  haveI : w.asIdeal.LiesOver (HeightOneSpectrum.under W.CoordinateRing w).asIdeal := by
    rw [HeightOneSpectrum.under_asIdeal]; infer_instance
  exact dvd_ord_functionFieldMap _ w hf hd

/-! ## The fibre is non-empty, and the transport runs backwards

`HeightOneSpectrum.under` sends a closed point of `K[W⁄K]` down to one of `F[W]`.  This section says
it is **surjective**: every closed point of `F(W)` is `under` some closed point of `K(W⁄K)`.  That
is Mathlib's `Ideal.exists_maximal_ideal_liesOver_of_isIntegral` at
`instIsIntegralCoordinateRingMap`
and `instFaithfulSMulCoordinateRingMap`, with one step of its own — the lemma produces an `Ideal`,
and a `HeightOneSpectrum` additionally needs it to be nonzero.

⚠️ **What this buys is a descent, and it does not need a value for the ramification index.**  The
transport above multiplies by `e(w ∣ v)`, and `## What is *not* here` records that nothing here says
`e` is `1`.  A consumer that compares two orders at the same place does not care: the same `e`
stands in front of both sides and `ramificationIdx'_functionFieldMap_ne_zero` cancels it.  So an
identity `n • divisor (functionFieldMap g) = divisor (functionFieldMap f)` proved over `K` comes
back down to `n • divisor W g = divisor W f` over `F`, for an arbitrary finite `K / F`.
-/

/-- **Every closed point of `F(W)` has a closed point of `K(W⁄K)` above it.**

⚠️ The `ne_bot` half is the part Mathlib's lemma does not supply.  It comes from the same
injectivity `instFaithfulSMulCoordinateRingMap` is built on: `Ideal.under` of `⊥` is the kernel of
`F[W] → K[W⁄K]`, so a `Q` lying over `v.asIdeal` with `Q = ⊥` would force `v.asIdeal = ⊥`. -/
theorem exists_liesOver [Module.Finite F K] (v : HeightOneSpectrum W.CoordinateRing) :
    ∃ w : HeightOneSpectrum (W.map (algebraMap F K)).CoordinateRing,
      w.asIdeal.LiesOver v.asIdeal := by
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (R := W.CoordinateRing) (S := (W.map (algebraMap F K)).CoordinateRing) v.asIdeal
  refine ⟨⟨Q, hQmax.isPrime, ?_⟩, hQ⟩
  rintro rfl
  refine v.ne_bot (hQ.over.trans ?_)
  rw [Ideal.under, ← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).mp
    (FaithfulSMul.algebraMap_injective W.CoordinateRing _)

/-- **`HeightOneSpectrum.under` is surjective**, which is `exists_liesOver` read through
`HeightOneSpectrum.under_asIdeal`.  This is the form the `∀ w` statements above are quantified by,
so it is what says those statements reach every `v`. -/
theorem exists_under_eq [Module.Finite F K] (v : HeightOneSpectrum W.CoordinateRing) :
    ∃ w : HeightOneSpectrum (W.map (algebraMap F K)).CoordinateRing,
      HeightOneSpectrum.under W.CoordinateRing w = v :=
  let ⟨w, hw⟩ := exists_liesOver W K v
  ⟨w, HeightOneSpectrum.ext hw.over.symm⟩

/-- **The descent of an order identity.**  If `n * ord (functionFieldMap g) = ord (functionFieldMap
f)` holds at every closed point of `K(W⁄K)`, it holds at every closed point of `F(W)`.

⚠️ **No value for the ramification index is used.**  At a given `v` the hypothesis is read at one
`w` above it, where both sides carry the same factor `e(w ∣ v)`;
`ramificationIdx'_functionFieldMap_ne_zero` makes that factor cancellable.  This is why
`## What is *not* here`'s missing `e = 1` does not block a descent, only an on-the-nose
transport. -/
theorem ord_eq_of_forall_ord_functionFieldMap_eq [Module.Finite F K] {n : ℤ}
    {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : ∀ w : HeightOneSpectrum (W.map (algebraMap F K)).CoordinateRing,
      n * ord w (functionFieldMap W K g) = ord w (functionFieldMap W K f))
    (v : HeightOneSpectrum W.CoordinateRing) :
    n * ord v g = ord v f := by
  obtain ⟨w, hw⟩ := exists_liesOver W K v
  haveI := hw
  have hwv := h w
  rw [ord_functionFieldMap W K v w hf, ord_functionFieldMap W K v w hg] at hwv
  refine mul_left_cancel₀ (a := (v.asIdeal.ramificationIdx' w.asIdeal : ℤ)) ?_ ?_
  · exact_mod_cast ramificationIdx'_functionFieldMap_ne_zero v w
  · rw [← hwv]; ring

/-- **The descent of a divisor identity.**  `n • divisor g = divisor f` may be proved over any
finite extension `K / F` and then read back over `F`.

This is the shape a descent argument ends on: the divisor identity is produced over a field where
enough points are rational, and the conclusion is wanted over the field one started from. -/
theorem divisor_eq_of_divisor_functionFieldMap_eq [Module.Finite F K] {n : ℤ}
    {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : n • divisor (W.map (algebraMap F K)) (functionFieldMap W K g)
      = divisor (W.map (algebraMap F K)) (functionFieldMap W K f)) :
    n • divisor W g = divisor W f := by
  ext v
  simpa using ord_eq_of_forall_ord_functionFieldMap_eq W K hf hg
    (fun w => by simpa using congrArg (fun D => D w) h) v

/-- **A function has trivial divisor exactly when its base change does.**

⚠️ This is `ord_functionFieldMap_eq_zero_iff` with the quantifier the absence section said it did
not have: that statement is an `iff` at one named `w` over one named `v`, and this one ranges over
both spectra.  The forward direction is `exists_liesOver`; the backward one is
`ord_functionFieldMap_under_eq_zero_iff`, which already quantified over `w` alone. -/
theorem divisor_functionFieldMap_eq_zero_iff [Module.Finite F K] {f : W.FunctionField}
    (hf : f ≠ 0) :
    divisor (W.map (algebraMap F K)) (functionFieldMap W K f) = 0 ↔ divisor W f = 0 := by
  constructor
  · intro h
    ext v
    obtain ⟨w, hw⟩ := exists_liesOver W K v
    haveI := hw
    have hw0 := congrArg (fun D => D w) h
    simp only [divisor_apply, Finsupp.coe_zero, Pi.zero_apply] at hw0 ⊢
    exact (ord_functionFieldMap_eq_zero_iff v w hf).mp hw0
  · intro h
    ext w
    have hv0 := congrArg (fun D => D (HeightOneSpectrum.under W.CoordinateRing w)) h
    simp only [divisor_apply, Finsupp.coe_zero, Pi.zero_apply] at hv0 ⊢
    exact (ord_functionFieldMap_under_eq_zero_iff W K w hf).mpr hv0

/-! ## Non-vacuity -/

section Nonvacuity

open EllipticCurves.Fixture Polynomial

/-! The certificate curve is `EllipticCurves.Fixture.y2EqX3SubX` at `R = ℚ` and the certificate
extension is `(X ^ 2 + 1 : ℚ[X]).SplittingField`.  ⚠️ **The extension is proper** —
`certRoot_not_mem_range` below — so nothing here is a statement about an isomorphism in disguise,
and `Module.Finite` over it is Mathlib's global instance on a splitting field, which is what
`instIsIntegralCoordinateRingMap` consumes.  The closed point is the one attached to the rational
point `(0, 0)` of the base-changed curve, and the function is the class of `x`, nonzero because
`XClass` and `genPsi` are. -/

/-- A root of `X² + 1` in its splitting field over `ℚ`.

⚠️ Built from `Polynomial.SplittingField.splits` rather than from `IsSplittingField.splits`:
`IsSplittingField ℚ (X² + 1).SplittingField (X² + 1)` is **not** found by typeclass search at this
pin — `Polynomial.IsSplittingField.splittingField` applies when supplied by hand and `inferInstance`
fails, even with the instance attribute set locally. -/
private noncomputable def certRoot : (X ^ 2 + 1 : ℚ[X]).SplittingField :=
  rootOfSplits (Polynomial.SplittingField.splits (K := ℚ) (f := (X ^ 2 + 1 : ℚ[X])))
    (by rw [Polynomial.degree_map, show (X ^ 2 + 1 : ℚ[X]).degree = 2 by compute_degree!]
        exact two_ne_zero)

private theorem certRoot_eval :
    ((X ^ 2 + 1 : ℚ[X]).map
      (algebraMap ℚ (X ^ 2 + 1 : ℚ[X]).SplittingField)).eval certRoot = 0 := by
  rw [certRoot]; exact eval_rootOfSplits _ _

/-- **The certificate extension is proper**: `X² + 1` has no rational root, so its root in the
splitting field is outside the image of `ℚ`. -/
private theorem certRoot_not_mem_range :
    certRoot ∉ Set.range (algebraMap ℚ (X ^ 2 + 1 : ℚ[X]).SplittingField) := by
  rintro ⟨q, hq⟩
  have h := certRoot_eval
  rw [← hq, eval_map, Polynomial.eval₂_hom] at h
  have hq0 : (q : ℚ) ^ 2 + 1 = 0 := by
    have := (map_eq_zero (algebraMap ℚ (X ^ 2 + 1 : ℚ[X]).SplittingField)).mp h
    simpa using this
  nlinarith [sq_nonneg (q : ℚ)]

private theorem equation_zero_zero_cert :
    ((y2EqX3SubX ℚ).map
      (algebraMap ℚ (X ^ 2 + 1 : ℚ[X]).SplittingField)).Equation 0 0 := by
  rw [equation_iff']
  simp [y2EqX3SubX, WeierstrassCurve.map]

/-- The certificate closed point: the one attached to `(0, 0)` on the base-changed curve.  ⚠️ Its
existence is what makes `ord_functionFieldMap_under`'s `∀ w` non-empty. -/
private noncomputable def certPoint :
    HeightOneSpectrum ((y2EqX3SubX ℚ).map
      (algebraMap ℚ (X ^ 2 + 1 : ℚ[X]).SplittingField)).CoordinateRing :=
  pointClosedPoint equation_zero_zero_cert

/-- The certificate function `x ∈ ℚ(W)` is nonzero. -/
private theorem genPsi_XClass_ne_zero :
    genPsi (y2EqX3SubX ℚ) (XClass (y2EqX3SubX ℚ) 0) ≠ 0 := by
  rw [ne_eq, ← map_zero (genPsi (y2EqX3SubX ℚ))]
  exact fun h => XClass_ne_zero (W' := y2EqX3SubX ℚ) 0 (IsFractionRing.injective _ _ h)

/-- **The base-change transport, with no hypothesis at all**, on `y² = x³ - x` over `ℚ` at the
closed point of `(0, 0)` over the proper quadratic extension `(X² + 1).SplittingField`. -/
private theorem ord_functionFieldMap_under_cert :
    ord certPoint
        (functionFieldMap (y2EqX3SubX ℚ) (X ^ 2 + 1 : ℚ[X]).SplittingField
          (genPsi (y2EqX3SubX ℚ) (XClass (y2EqX3SubX ℚ) 0)))
      = ((HeightOneSpectrum.under (y2EqX3SubX ℚ).CoordinateRing certPoint).asIdeal.ramificationIdx'
          certPoint.asIdeal : ℤ)
        * ord (HeightOneSpectrum.under (y2EqX3SubX ℚ).CoordinateRing certPoint)
            (genPsi (y2EqX3SubX ℚ) (XClass (y2EqX3SubX ℚ) 0)) :=
  ord_functionFieldMap_under _ _ certPoint genPsi_XClass_ne_zero

private theorem equation_zero_zero_base : (y2EqX3SubX ℚ).Equation 0 0 := by
  rw [equation_iff']
  simp [y2EqX3SubX]

/-- The certificate closed point **of the base curve**: the one attached to `(0, 0)` on
`y² = x³ - x` over `ℚ` itself.  `certPoint` is its analogue upstairs, and the two are different
objects over different rings — which is the whole content of `exists_under_eq_cert`. -/
private noncomputable def certPointBase :
    HeightOneSpectrum (y2EqX3SubX ℚ).CoordinateRing :=
  pointClosedPoint equation_zero_zero_base

/-- **The fibre over a named closed point of a named curve is non-empty**, over the same proper
quadratic extension the rest of this section uses.

⚠️ This is what makes `exists_under_eq` non-vacuous in the only way that counts: over an
algebraically closed base, or along an isomorphism, `under` is a bijection and the statement is
free.  Here `certRoot_not_mem_range` says the extension is proper. -/
private theorem exists_under_eq_cert :
    ∃ w : HeightOneSpectrum (((y2EqX3SubX ℚ).map
        (algebraMap ℚ (X ^ 2 + 1 : ℚ[X]).SplittingField)).CoordinateRing),
      HeightOneSpectrum.under (y2EqX3SubX ℚ).CoordinateRing w = certPointBase :=
  exists_under_eq _ _ certPointBase

end Nonvacuity

end WeierstrassCurve.Affine.CoordinateRing
