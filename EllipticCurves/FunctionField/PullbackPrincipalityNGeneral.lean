/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import EllipticCurves.FunctionField.DivisorBaseChangeRationalPoint
import EllipticCurves.FunctionField.DivisorGaloisDescentNsmul
import EllipticCurves.FunctionField.FunctionFieldBaseChangeN
import EllipticCurves.FunctionField.PullbackPrincipalityNRationalTorsionHprin

/-!
# `[n]∗((S) − (O))` is `n` times a principal divisor, by descent from an ABSTRACT finite Galois `N`

`EllipticCurves.FunctionField.PullbackPrincipalityNRationalTorsionHprin` discharges `hprin` at a
general `n` over an arbitrary field, but only from two rationality hypotheses over the base:
`hcard : #E[n] = n²` and a point `P` with `[n]P = S`.  **This file moves both hypotheses up to a
finite Galois extension `N / F` and brings the conclusion back down.**  It is the general-`n`
analogue of `exists_nsmul_divisor_eq_divisor_mulByThreeEndo_of_galois`
(`EllipticCurves.FunctionField.PullbackPrincipalityThreeGeneral`), and it is rung 3 of `#962`'s
general-`n` ladder.

⚠️ **`N` is ABSTRACT here and no tower is built.**  Constructing the field over which the two
hypotheses become *theorems* — `halvingGaloisField` at `n = 2`, `triplingGaloisField` at `n = 3`,
and a tower of unmeasured depth at a general index — is rung 4, and so is the unconditional
`…_general` headline it unlocks.  This file stops at the descent.

⚠️ **Abstracting `N` is a measurement and not a preference**, and it is
`PullbackPrincipalityThreeGeneral`'s own finding re-used rather than re-derived: transcribing the
`n = 2` proof with the tower inlined exceeds the **default** heartbeat limit at `n = 3` already,
because `triplingGaloisField` is a five-layer chain of splitting fields that unification must
unfold.  **This file carries no `set_option maxHeartbeats`**, and the argument for keeping `N`
abstract only strengthens with the depth of whatever rung 4 builds.

## The route, in four steps

1. `algebraMap_ofNat_ne_zero` and `map_intCast` carry `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` up to
   `N`.
2. `divisor_functionFieldMap_eq_single`
   (`EllipticCurves.FunctionField.DivisorBaseChangeRationalPoint`) carries `div f = n·(S)` up to `N`
   **on the nose** — the fibre over the closed point of a *rational* point is a singleton with
   `e = 1` there.
3. `exists_nsmul_divisor_eq_divisor_mulByNEndo_of_card` over `N` (`#2293`) produces a `g` with
   `n · div g = div ([n]∗ f)` upstairs.
4. `exists_nsmul_divisor_eq_of_functionFieldMap`
   (`EllipticCurves.FunctionField.DivisorGaloisDescentNsmul`) brings the identity back to `F`, by
   Hilbert 90 at the finite level.  ⚠️ The function it returns is **not** the descent of `g`.

⚠️ **The `F̄` route is closed at every index and this is not a matter of taste**: Mathlib's
Hilbert 90 is `[FiniteDimensional]`-only at the pin, so `H¹(Gal(F̄/F), F̄ˣ) = 0` is unavailable and
the finite extension is the route rather than a convenience.

## ⚠️ Seven of the eight inputs were ALREADY general at source, and the two that were not are named

Re-resolved declaration by declaration at `3f9e323`, against the elaborated type and not the
`theorem` line:

| input | index binder at source |
|---|---|
| `algebraMap_ofNat_ne_zero` | `{n : ℕ} [n.AtLeastTwo]` — general |
| `WeierstrassCurve.map_nonsingular` | Mathlib, index-free |
| `divisor_functionFieldMap_eq_single` | `{n : ℤ}`, `[Module.Finite F K]` — general |
| `exists_nsmul_divisor_eq_of_functionFieldMap` | `{n : ℕ} (hn : n ≠ 0)`, finite Galois — general |
| `mulByNEndo` / `mulByNEndo_injective` | `(n : ℕ)` — general |
| `functionFieldMap_mulByNEndo` | `{n : ℕ}` — general |
| `exists_nsmul_divisor_eq_divisor_mulByNEndo_of_card` | `{n : ℕ}` — general, and it is `#2293` |
| ⚠️ the torsion-membership bridge | `n = 3`-specific at source; **replaced, see below** |

**So this rung is assembly.**  ⚠️ **It is not assembly with nothing in it, and the two findings
below are what it cost.**

### ⚠️ FINDING 1 — the ONE hypothesis the general-`n` descent binds is the endomorphism's own index

`mulByThreeEndo h2 h3` is indexed by two *numeral* facts, and `algebraMap_ofNat_ne_zero` transports
both to `N` for free — which is why the `n = 3` descent needs no extra binder.  `mulByNEndo n h` is
indexed by `h : Transcendental F (x([n]𝒫))` instead, and ⚠️ **`functionFieldMap_mulByNEndo` takes
the transcendence over `F` *and* over `N` because neither implies the other at that generality**:
its own module docstring — under
`## ⚠️ Two transcendence hypotheses, over two different fields, and neither implies the other` in
`EllipticCurves.FunctionField.FunctionFieldBaseChangeN` — says *"Do not try to transport one into
the other"* in terms.  ⚠️⚠️ **AND `h'` IS NO LONGER A BINDER OF EITHER THEOREM BELOW, BECAUSE IT IS
DERIVABLE FROM WHAT THEY ALREADY BIND.**  ⚠️ **The first wording of this finding closed with** *"So
`h'` over `N` is a hypothesis here, and it is the one place where the general index costs a binder
that `n = 2` and `n = 3` do not pay"*, **and BOTH of its conjuncts are RETIRED**: `h'` is a `have`
inside the descent proof below — `exists_gS_n_of_galois` never sees it at all, because it routes
through that theorem — and the one binder the numeral forms do not pay is `h` over `F`, for the
reason that theorem's own docstring gives: `mulByNEndo n h` *mentions* it, so it is data for the
statement rather than an assumption of it.  ⚠️ **The ⚠️-marked claim above this one is NOT what was
retired and is exact**: that `functionFieldMap_mulByNEndo` takes the transcendence over both fields,
and that neither of the two *statements* implies the other, both still hold and were re-verified. ⚠️
**What does not follow from it, and what the retired wording asserted, is that a caller at a general
index must therefore SUPPLY the `N`-side one.**
`transcendental_xCoord_nsmul_genericPoint_baseChange_of_intCast_ne_zero`
(`EllipticCurves.FunctionField.MulByNXCoordFormula`) is the `F`-side producer read on `W⁄L` at `L`,
with its two numeral hypotheses transported along `algebraMap F L`, and it binds nothing beyond
`(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` — **no algebraic closure, no `[FiniteDimensional F L]` and no
`3`-smoothness.**  So the `N`-side fact CAN be bought from the base hypotheses rather than
transported from the `F`-side fact, which is the distinction the retired clause collapsed.  ⚠️ **As
of `#2306` round 2 the proofs below buy it from `hP` through the criterion instead, so this producer
is an alternative route and not the one taken — see FINDING 1.**  ⚠️ **This retires
the `3`-smooth route as the general-index answer.**  That route —
`transcendental_xCoord_nsmul_of_smooth` (`EllipticCurves.FunctionField.MulByNComposition`), at the
price of `(2 : F) ≠ 0`, `(3 : F) ≠ 0`, `n ≠ 0` and `∀ p ∈ n.primeFactors, p = 2 ∨ p = 3` — remains
available, and it is no longer the cheapest at an unknown index.  ⚠️ **`(3 : F) ≠ 0` is named in
that list because it is a real difference from this file's own binders**, under
`MulByNComposition`'s standing ruling that `(2 : F) ≠ 0` and `(3 : F) ≠ 0` *"stay named, and every
headline above that makes a hypothesis-list claim carries them"*.

⚠️⚠️ **THE PRODUCERS ARE FOUR AND NOT THREE, AND THE FOURTH IS THE ENGINE OF EXACTLY ONE OF THE
OTHERS** — this census is keyed to the signatures and not to the `transcendental_xCoord_nsmul_of_*`
naming, which is what hid the fourth from this finding's first wording and from the two notes this
rung's thread carried before its round 1.  ⚠️ **That *one* is a transitive measurement and not a
name grep**: of the other three only `_of_isAlgClosed` reaches the criterion through any chain of
proof terms at all, and `…_of_intCast_ne_zero` and `_of_smooth` each argue independently — ⚠️ **as
does `transcendental_xCoord_three_nsmul`, which the walk carried as a fourth row and which is the
fixed-index producer of the paragraph below, no member of this census.**  ⚠️⚠️ **Both figures are
exact and they are over DIFFERENT populations: the CENSUS is four and its remainder is three, while
the WALK ran over that remainder plus the fixed-index producer — four rows.**  The walk is over the
whole transitive closure of their proof terms and not over their statements.  The four producers:

* ⚠️ `transcendental_xCoord_nsmul_genericPoint` — **the criterion**, whose own docstring title is
  that word in those terms.  Binds one `T : W.Point` with `n • T ≠ 0` and ⚠️ **no field hypothesis
  whatever**, so `((n : ℤ) : F) = 0` has nothing here to meet: **it applies there, and its
  availability is invariant in the index.**
* `…_nsmul_genericPoint_of_intCast_ne_zero`, and its `baseChange` form used below.  Binds
  `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`.  ⚠️ **Inconsistent with `((n : ℤ) : F) = 0` outright: it
  binds the negation.**
* `…_nsmul_of_isAlgClosed`.  Binds `[IsAlgClosed F]`, `(2 : F) ≠ 0` and `n ≠ 0` — ⚠️ **no condition
  on `((n : ℤ) : F)` at all, and it applies there**, on the witness below.
* `…_nsmul_of_smooth`.  Binds `(2 : F) ≠ 0`, `(3 : F) ≠ 0`, `n ≠ 0` and `3`-smoothness.  ⚠️⚠️ **Its
  hypotheses are JOINTLY INCONSISTENT with `((n : ℤ) : F) = 0`, so it does NOT apply there**:
  `(n : F) = 0` with `n ≠ 0` forces `ringChar F ∣ n`, `3`-smoothness puts that prime in `{2, 3}`,
  and `(2 : F) ≠ 0` with `(3 : F) ≠ 0` rules out both.

The criterion and `_of_isAlgClosed` are in the same file,
`EllipticCurves.FunctionField.MulByNTranscendence`, and ⚠️ **the second is a two-line corollary of
the first** — it buys the criterion's `T` from `exists_nsmul_ne_zero_of_isAlgClosed`, and that is
all the closure is for.

⚠️⚠️ **AND A SECOND CELL OF THIS PARAGRAPH WAS WRONG, AND NO REVIEW EVER CHARGED IT**: the heading
above read *"THE ENGINE OF TWO OF THE OTHERS"* until this round, and the proof-term walk says
**one**.  ⚠️ **EXACTLY ONE review ever read that cell, and it did not test it**: the cell entered at
round 2 of `#2296`, and round 2 drew a single review.  ⚠️ **The first wording of this sentence said
*"two independent reviews"*, which is the count over the PARAGRAPH and not over the cell** — the
paragraph's earlier three-member form drew two reviews, and neither could test a cell that did not
yet exist.  A count standing beside a correct structural claim borrows its credibility, which is
exactly the shape of the applicability cell below.  **Walk the proof terms: a name grep over callers
is not a reading of the relation.**

⚠️ **The first wording of this paragraph said `_of_smooth`** *"remains the only one of the three
producers that applies when `((n : ℤ) : F) = 0`"*, **and that is RETIRED as false in three ways and
not two.**  `_of_isAlgClosed` binds no condition on `((n : ℤ) : F)` whatever, and
`MulByNXCoordFormula` rules exactly that configuration in its *"incomparable, not nested"* paragraph
— *"the merged one applies and this one does not"* — immediately above the one this file draws the
base-change reading from.  And the criterion binds no field condition either.  ⚠️⚠️ **The third way
is the member the universal names: `_of_smooth` is not in that class at all.**  So the count is
**TWO of the four and not three** — the criterion and `_of_isAlgClosed` apply at
`((n : ℤ) : F) = 0`, and the other two are each inconsistent with it.

⚠️⚠️ **One field — the field where `(3 : F) ≠ 0` dies — is a CERTIFICATE for exactly ONE of those
four rows and an ILLUSTRATION for two, and the first wording of this sentence had it as a bare
*"settles three"*.**  Over `F = AlgebraicClosure (ZMod 3)` at `n = 3` the four conditions
`[IsAlgClosed F]`, `n ≠ 0`, `(2 : F) ≠ 0` and `((n : ℤ) : F) = 0` hold **together** — so
`_of_isAlgClosed`'s *applies* row is a positive witness rather than an absence of a refutation, and
⚠️ **that is the certificate: an *applies* row is the only kind a single field can settle.** ⚠️
**The two *inconsistent* rows are universal and are argued, not witnessed**: `…_of_intCast_ne_zero`
binds the negation of `((n : ℤ) : F) = 0` outright, and `_of_smooth`'s list is ruled by the
`ringChar F ∣ n` step above.  This same field merely ILLUSTRATES both — `(3 : F) = 0` is exactly the
binder `_of_smooth` asks for and cannot have, and `((n : ℤ) : F) ≠ 0` fails there too.  ⚠️⚠️
**Granting `_of_smooth` that illustration and not `…_of_intCast_ne_zero` is the asymmetry the old
count hid.** The criterion's row needs no field at all: it binds no field hypothesis, so nothing
about `F` can settle it or disturb it.

⚠️⚠️ **AND THE CELL THAT MOVED IS THE ONE A LATER READING COULD NOT RECONSTRUCT: restoring
`(3 : F) ≠ 0` to `_of_smooth`'s list is what emptied its regime.**  The round that first wrote this
paragraph had dropped that binder, and with it dropped `_of_smooth` *did* apply at
`((n : ℤ) : F) = 0` — characteristic `3` at `n = 3` meets every hypothesis it then had.  ⚠️ **The
repair that restored the binder and the applicability claim that survived it were in the same diff,
and no build, lint, hygiene or render gate can see that.**  **When a round restores a dropped
hypothesis, re-read every applicability claim in the same paragraph.**

⚠️⚠️ **AND THE CRITERION DISCHARGES `h'` FROM `hP` ALONE, WHICH IS STRICTLY STRONGER THAN THIS
FINDING'S HEADLINE AND IS THE ROUTE THE PROOFS BELOW TAKE (`#2306`).**  `hP` is already a
hypothesis of
both theorems, and it is exactly a `P : (W⁄N).Point` whose `n • P` is a `Point.some` and so nonzero
— which is the criterion's `hT` and nothing else.  So `h'` costs **no** `h2`, **no** `hn`, no
closure and no smoothness.  ⚠️ **One instance step is the whole remaining cost, and it is a
one-liner**: the criterion is stated `open Classical in`, so its `n • T` reads
`Point.instAddCommGroup` at `fun a b => Classical.propDecidable (a = b)` where `hP`'s reads it at
this file's `[DecidableEq N]`, and the two terms are not syntactically equal; `Subsingleton.elim` on
the `DecidableEq N` instance rewrites one into the other.  ⚠️ **Measured both ways round rather than
argued**: without the bridge the application fails with a printed instance mismatch between those
two terms, and with it the derivation compiles in rung 3's own binder shape, `[DecidableEq N]` and
all.

⚠️ **The proofs below TAKE the criterion route as of `#2306` round 2, and this paragraph read**
*"The proofs below keep the `h2` / `hn` route anyway, and that is a choice and not an oversight"*
**until then.**  ⚠️⚠️ **What has not changed is the measurement that wording rested on: `h2` and
`hn` are not removable here, so the re-route shortens no signature** — `h2` still buys `h2'`, `hn`
still buys both `hn0` and `hnN`, and `hnN` is interderivable with `hn` and is held by `…_of_card`.
⚠️ **It was taken anyway for the reason `#2306` gives: strictly fewer dependencies for the same line
count, and an `N`-side fact independent of the index arithmetic**, which is what rung 4 reads.  The
prior wording made the re-route conditional on `((n : ℤ) : F) ≠ 0` leaving the statement, and
`#2306` round 1 measured that it cannot.

⚠️ **The consequence is the one worth recording: `#962`'s unconditional general-`n` headline is not
`3`-smooth on this binder's account**, and ⚠️ **on the criterion's account the `N`-side
transcendence does not need `((n : ℤ) : F) ≠ 0` either.**  What the headline still needs over the
tower is `#E[n] = n²` and the `n`-divisibility of `S`.  ⚠️ **The `n = 3` recovery below discharges
NEITHER of those two** — it binds `hcard` and `hP` exactly as this file does.  The transcendence
producer is a separate difference and is worth naming on its own: at a fixed numeral index
`transcendental_xCoord_three_nsmul` (`EllipticCurves.FunctionField.MulByNPullback`) binds
`(2 : F) ≠ 0` and `(3 : F) ≠ 0`, which the recovery passes, and ⚠️ **no smoothness side condition**
— so it is what discharges `h` there.

⚠️⚠️ **THE COUNT CLAIMS OF THIS FINDING ARE NOW CENSUSED, WITH THEIR POPULATION PUBLISHED.**  The
reason is `#2309`'s: three rounds of `#2296` *"have now each repaired a count in this paragraph and
each introduced another"*, and a census of them with its population published is what breaks that.
**Population:** every line of this `### ⚠️ FINDING 1`, from its heading down to the last non-blank
line before this paragraph — **136** lines at this round's head, and **122** at `5710234`.  ⚠️ **THE
TWO BOUNDS ARE DIFFERENT OBJECTS AND A RE-RUNNER AT A THIRD REF HAS TO CHOOSE BETWEEN THEM — NOT BY
THE REF'S NAME**: the lower bound is this census paragraph at any ref that carries it, and
`### ⚠️ FINDING 2` at any ref that does not, because at `5710234` this paragraph did not exist.
**Those two — this paragraph, and that heading — are the whole of the choice.**  ⚠️ **This paragraph
is excluded from its own population, which is the only way the figure is a fixed point**; re-run the
sweep after any edit ABOVE it.  **Stage 1, mechanical and the reproducible half:** mask every
backtick span and every `*"…"*` marked quotation, then take every word-boundary occurrence of
`one`…`ten`, `both`, `single`, `either`, `neither` and every bare decimal integer — **56**
candidates at `5710234`, **68** at this head.  ⚠️ **Stage 1 OVER-counts on purpose**: it keeps
section, round and rung labels and the pronoun uses of *one*, because for a completeness sweep a
superset is the safe direction.  **Stage 2 is a reading and not a measurement**: it returns **5**
hits at `5710234` and ⚠️ **0 at this head, because this round repairs all five** — the producer
clause above, the *settles* count, the review count in **two** sites in one sentence pair (*"either
review"* and *"two independent reviews"*), and *"two notes on `#2296`"*, whose population was a
thread that grows.  ⚠️⚠️ **A count claim is CLEARED only when the text names the population it is
counted over AND that population is closed.  A count repaired without its population named is a hit
that still reads as a clearance.**

### ⚠️ FINDING 2 — the torsion bridge has no division polynomial at a general `n`

⚠️ **The point-level route needed a new brick, because `basePointMap` cannot carry a `map_*`
lemma.**  That is the second half of this finding and it is stated here rather than in the
heading, because an ATX heading is one source line.

`n = 2` transports `mem_torsion_two_some_iff` through a `congrArg` on the coordinates and `n = 3`
re-derives membership from `Ψ₃.eval x = 0`, which base-changes as a `Polynomial.eval`.  ⚠️ **At a
general `n` there is no such polynomial**, so the only route is the point-level one:
`mem_torsion_iff` (`EllipticCurves.Torsion.Defs`) is already `{n : ℕ}`, so what is needed is that
`n • S = 0` survives base change — one application of `map_nsmul` to an additive map on points.

⚠️⚠️ **`basePointMap` (`EllipticCurves.FunctionField.FunctionFieldBaseChangeN`) is that map and NO
`map_*` lemma can be applied to it in a context carrying `[DecidableEq F]`, which is measured and
not supposed.**  It is declared under `open Classical in`, so the `AddZeroClass W.Point` in its own
arrow type comes from `Classical.decEq F`; synthesising
`AddMonoidHomClass (W.Point →+ (W⁄N).Point) W.Point (W⁄N).Point` then **fails**, because instance
search produces the `[DecidableEq F]`-derived structure instead and the two do not match.  The
failure is the same whether `map_nsmul` is applied as a term or fired by `rw`, and adding
`open Classical in` to the consumer does not fix it.  ⚠️ **The working form is Mathlib's
`Point.map (Algebra.ofId F N)` under the ambient `[DecidableEq F]` and `[DecidableEq N]`** — which
`basePointMap` is a `Classical` wrapper *of* — with the `Point.some` computation left to
definitional unfolding rather than to `Point.map_some`, whose own `(W⁄F).Point` / `W.Point` framing
`rw` will not match either.  That is `mem_torsion_baseChange_of_nsmul_eq_zero` below.

⚠️ **Consequence for the signatures, and it is why the descent step takes its torsion hypothesis
over `N`.**  The bridge binds `[DecidableEq F]`; the descent step does not want to.  Taking
`hS` **over `N`** keeps the `omit [DecidableEq F]` that the `n = 3` form has *and* is a strictly
weaker hypothesis — the `F`-form implies it through the bridge — so the theorem is stronger, not
weaker, for it.  `exists_gS_n_of_galois` takes the `F`-form and pays the bridge, because
`exists_gS_n` binds `[DecidableEq F]` regardless.

## Main statements

Reach clauses below are complete, per `README.md` `## Docstring conventions` option (a), and are
read off the **elaborated type**.

* `WeierstrassCurve.Affine.exists_nsmul_divisor_eq_divisor_mulByNEndo_of_galois` — the descent step.
  ⚠️ **No `[DecidableEq F]`**, matching the `n = 3` form; it binds `[W.IsElliptic]`, which
  `mulByNEndo`'s index forces since `genericPoint` is defined only for an elliptic curve.  Reach:
  `(2 : F) ≠ 0`, `((n : ℤ) : F) ≠ 0`, non-constancy of `x([n]𝒫)` over `F` — ⚠️ **over `F` alone;
  the `N`-side statement was a binder until FINDING 1 and is now produced inside** —
  `#E[n] = n²` over `N`, an arbitrary finite Galois `N / F` with `[DecidableEq N]`, the
  nonsingularity of the `F`-rational `S = (x, y)`, the `n`-torsion of `S` **over `N`**, a point `P`
  of `E(N)` with `[n]P = S`, and a nonzero `f` with `div f = n·(S)`.
* `WeierstrassCurve.Affine.mem_torsion_baseChange_of_nsmul_eq_zero` — the bridge of FINDING 2:
  `n • S = 0` over `F` gives `S ∈ E(N)[n]` at every `n`.  ⚠️ **It binds `[DecidableEq F]` and
  `[DecidableEq N]` and no `[W.IsElliptic]`** — it is a statement about the group of points and
  about nothing else, and it is the only declaration here that is not assembly.
* `WeierstrassCurve.Affine.exists_gS_n_of_galois` — rung 5 of the Weil pairing over the same data,
  producing the `f` itself.  Reach: the descent step's list with `hS` read over `F` instead of over
  `N`, without the quantified `f`, and ⚠️ **with `[DecidableEq F]` added**, which `exists_gS_n`
  (`EllipticCurves.FunctionField.NthRootOfPullbackN`) binds.

`#print axioms` over all three returns exactly `{propext, Classical.choice, Quot.sound}`; `sorry`
and `sorryAx` are absent.

## Recovery

`#907`'s rule.  The `example` in `## Recovery` restates
`exists_nsmul_divisor_eq_divisor_mulByThreeEndo_of_galois` **verbatim** — same hypothesis list, same
`omit [DecidableEq F]`, same conclusion in terms of `mulByThreeEndo h2 h3` — and proves it from the
general form.  ⚠️ **The `omit` is part of the restatement and not an accident**: the rule
this file's own dependency `EllipticCurves.FunctionField.PullbackPrincipalityNRationalTorsionHprin`
states applies here — "an `example` that quietly keeps an instance its original omits restates
something *weaker* than the theorem it claims to subsume, and the signatures match either way" —
whose earliest home in the tree is `EllipticCurves.FunctionField.PullbackPrincipalityN`.  The two
`mulByNEndo` indices are interchangeable because `Transcendental` is a `Prop`, and
`mulByNEndo_three` (`EllipticCurves.FunctionField.MulByNPullback`) is the bridge to the numeral
endomorphism.

⚠️ **The `n = 2` `…_of_galois` is NOT recovered, because there is none to recover.**
`PullbackPrincipalityTwoGeneral` inlines its tower and states no abstract-`N` descent step, which
is `PullbackPrincipalityThreeGeneral`'s *"do NOT transpose from `n = 2`"* warning read from the
other side.

## Non-vacuity — STATED and inherited, not re-derived

`#916`'s rule, and `#2295`'s own instruction that a rung which silently drops its predecessor's
vacuity disclosure has un-published it.

⚠️ **`#2293` confines its certificate to `n = 2`**: *"`n = 2` is the only index at which the
`_of_card` hypotheses are certified jointly satisfiable on this board"*, because `hcard` at any
`n ≥ 3` forces `μ_n ⊆ F` and admits no `ℚ` certificate — the obstruction
`PullbackPrincipalityNRationalTorsion`'s `## Non-vacuity` section records.  **That disclosure is
inherited here unchanged and no certificate is claimed at any index.**

⚠️ **One thing does change and it is worth stating, because it is the whole point of the rung:**
this file's `hcard` is over `N` and not over `F`, so the `μ_n ⊆ F` obstruction is no longer an
obstruction to the *hypothesis* — it is what forces `N ≠ F`, and producing such an `N` is rung 4.
**Until rung 4 lands, the only `N` for which this file's hypotheses are certified satisfiable is
`N = F` at `n = 2`**, where the statement collapses to `#2293`'s `exampleRungFiveGeneral` and
certifies nothing new.  ⚠️ **No `example` below asserts otherwise**, and the reason no inhabitation
is exhibited is this and not an oversight.

## ⚠️ What is *not* here

* **The general-`n` Galois tower** and the unconditional `…_general` headline — `#2296`.
  ⚠️ **The two towers already built are THREE named floors each, and four and five field
  extensions** — `EllipticCurves.Torsion.TriplingGaloisTower` states the unit distinction in terms,
  *"Three named floors are five field extensions"*, and `n = 2`'s middle floor hides one the same
  way `n = 3`'s hide two: `halvingField` is itself *"the two-step tower"*
  (`EllipticCurves.Torsion.HalvingExtension`) and `HalvingGaloisTower` names the hidden floor as
  *"the intervening `K₂`"*.  ⚠️ **Quote this pair in ONE unit or it reads as a step that is not
  there**: `3 / 3` named, `4 / 5` extensions.  ⚠️ **The inference this bullet used to draw from the
  pair — *"so its depth at a general index is unbounded"* — is RETIRED: two points do not determine
  the sequence, and the one-extension step is accounted for by the `n = 2` tower LACKING a layer
  rather than by the `n = 3` one gaining a growing number of them** (at `n = 2` the roots of `Ψ₂Sq`
  are the `2`-torsion `x`-coordinates, whose `y` is forced, so the division field needs no
  `y`-layer, where at `n = 3` it is `Ψ₂SqRootPoly` over `Ψ₃`'s splitting field).  ⚠️ **In named
  units the step is ZERO and the retirement is stronger still.**  **What the general depth is is
  open and is rung 4's to measure**; nothing here asserts it either way.
* **`exists_gS_n_general`** — it instantiates the tower, so it is rung 4's.
* **Any weakening of `hcard` or of `hP`.**  Both are hypotheses here, moved to `N` and not removed.
* **Re-derivation of the seven already-general inputs.**  Each binder was re-resolved once at
  source and then consumed.
* **No degree and no Galois group.**  `[N : F]` is not computed, `Gal(N/F)` is not identified, and
  nothing below says `F ⊊ N`.
* **Nothing about a non-rational `S`.**  Every statement is at an affine point of `W(F)`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8 (the Weil pairing)
  and VIII.2 (Hilbert 90).
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [DecidableEq F] [W.IsElliptic]

omit [W.IsElliptic] in
/-- **`n`-torsion of an `F`-rational point survives base change, at every `n`.**  Stated as the
group equation `n • S = 0` downstairs and as `torsion` membership upstairs, which is the pair the
descent step consumes.

⚠️ **This is the general-`n` replacement for the division-polynomial bridges the numeral files
use** (`mem_torsion_two_some_iff` at `n = 2`, `Ψ₃.eval x = 0` at `n = 3`), and it is the one
declaration in this file that is not assembly.  See FINDING 2 in the module docstring for why it
goes through Mathlib's `Point.map` rather than through `basePointMap`, and why no `map_*` lemma
applies to the latter.

⚠️ **No `[W.IsElliptic]`**: it is a statement about the group of points. -/
theorem mem_torsion_baseChange_of_nsmul_eq_zero (N : Type*) [Field N] [Algebra F N]
    [DecidableEq N] {n : ℕ} {x y : F} (hns : W.Nonsingular x y)
    (hS : n • Point.some x y hns = 0) :
    Point.some (algebraMap F N x) (algebraMap F N y)
      ((W.map_nonsingular (algebraMap F N).injective x y).mpr hns) ∈ (W⁄N).torsion n := by
  have key := map_nsmul (Point.map (W' := W) (Algebra.ofId F N)) n (Point.some x y hns)
  rw [hS, map_zero] at key
  exact mem_torsion_iff.mpr key.symm

omit [DecidableEq F] in
/-- **The descent step at a general `n`**, over an arbitrary field `F` with `(2 : F) ≠ 0` and
`((n : ℤ) : F) ≠ 0` and an arbitrary finite Galois extension `N / F` over which `#E[n] = n²` and `S`
is `n` times a point: for a nonsingular `F`-rational `S = (x, y)` that is `n`-torsion over `N` and a
nonzero `f` with `div f = n·(S)`, the pullback `[n]∗ f` is `n` times a principal divisor **over
`F`**.

Steps 1–4 of the route in the module docstring; `N` is a variable here and rung 4 (`#2296`) is what
instantiates it.

⚠️ **`[DecidableEq F]` is NOT bound**, matching the `n = 3` form — the decidability the `torsion`
subgroup needs is `[DecidableEq N]`, upstairs, and the rest is supplied by `classical` inside.
⚠️ **`[W.IsElliptic]` IS bound**, and it is read off the elaborated type rather than off the
`variable` line: `mulByNEndo`'s index mentions `genericPoint`, which exists only for an elliptic
curve, and `(W⁄N).IsElliptic`, which `…_of_card` over `N` wants, is synthesised from it.

⚠️ **`hS` is read over `N` and not over `F`, deliberately.**  The `F`-form implies it through
`mem_torsion_baseChange_of_nsmul_eq_zero`, so this is the weaker hypothesis and the stronger
theorem; taking the `F`-form instead would drag `[DecidableEq F]` into the signature for nothing.

⚠️ **The `N`-side transcendence is NOT a binder** — see FINDING 1.  `functionFieldMap_mulByNEndo`
does need it, and it is produced inside from `hP` ALONE by
`transcendental_xCoord_nsmul_genericPoint` (`EllipticCurves.FunctionField.MulByNTranscendence`,
**the criterion**), across one `convert … using 9` instance bridge, rather than asked of the caller.
⚠️ **This clause read** *"it is produced inside from `h2` and `hn` by
`transcendental_xCoord_nsmul_genericPoint_baseChange_of_intCast_ne_zero`"* **until `#2306` round
2**; that route also works and spends two hypotheses this one does not.  ⚠️ **`h` over `F` is a
binder and cannot be removed the same way**, and the reason is the conclusion rather than the proof:
`mulByNEndo n h` *mentions* it, so it is data for the statement and not an assumption of it — `h2`
and `hn` would produce it too.

⚠️ **The `g₀` this returns is not the base change of the `g` obtained over `N`**, and is not claimed
to be: only its divisor identity descends. -/
theorem exists_nsmul_divisor_eq_divisor_mulByNEndo_of_galois (N : Type*) [Field N]
    [Algebra F N] [FiniteDimensional F N] [IsGalois F N] [DecidableEq N]
    {n : ℕ} (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hcard : Nat.card ((W⁄N).torsion n) = n ^ 2)
    {x y : F} (hns : W.Nonsingular x y)
    (hS : Point.some (algebraMap F N x) (algebraMap F N y)
      ((W.map_nonsingular (algebraMap F N).injective x y).mpr hns) ∈ (W⁄N).torsion n)
    (hP : ∃ P : (W⁄N).Point, n • P
      = Point.some (algebraMap F N x) (algebraMap F N y)
        ((W.map_nonsingular (algebraMap F N).injective x y).mpr hns))
    {f : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint hns.left) (n : ℤ)) :
    ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
      n • divisor W g₀ = divisor W (mulByNEndo n h f) := by
  classical
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨P, hPeq⟩ := hP
  have h' : Transcendental N (n • genericPoint (W := W⁄N)).xCoord := by
    have hT : n • P ≠ 0 := ne_of_eq_of_ne hPeq (Point.some_ne_zero _)
    refine transcendental_xCoord_nsmul_genericPoint n (T := P) ?_
    convert hT using 9
  have h2' : (2 : N) ≠ 0 := algebraMap_ofNat_ne_zero h2
  have hnN : ((n : ℤ) : N) ≠ 0 := by
    rw [← map_intCast (algebraMap F N) (n : ℤ), ne_eq, map_eq_zero]
    exact_mod_cast hn
  have hns' : (W⁄N).Nonsingular (algebraMap F N x) (algebraMap F N y) :=
    (W.map_nonsingular (algebraMap F N).injective x y).mpr hns
  have hf' : functionFieldMap W N f ≠ 0 :=
    (map_ne_zero_iff _ (functionFieldMap_injective W N)).mpr hf
  have hfdiv' : divisor (W⁄N) (functionFieldMap W N f)
      = Finsupp.single (pointClosedPoint hns'.left) (n : ℤ) :=
    divisor_functionFieldMap_eq_single N hns.left hf hfdiv
  obtain ⟨g, hg, hgdiv⟩ :=
    exists_nsmul_divisor_eq_divisor_mulByNEndo_of_card h2' hnN h' hcard hns' hS hPeq hf' hfdiv'
  have hz : mulByNEndo n h f ≠ 0 :=
    (map_ne_zero_iff _ (mulByNEndo_injective n h)).mpr hf
  refine exists_nsmul_divisor_eq_of_functionFieldMap N hn0 hz hg ?_
  rw [hgdiv, functionFieldMap_mulByNEndo h h']
  rfl

/-- **Rung 5 of the Weil pairing at a general `n`, by descent from an abstract finite Galois `N`**:
for a nonsingular `F`-rational `n`-torsion point `S` there are a principal `f_S` with
`div f_S = n·(S)` and a nonzero `g_S` with `u · g_S ^ n = [n]∗ f_S` for a unit `u` of `F[W]`.

`exists_gS_n` (`EllipticCurves.FunctionField.NthRootOfPullbackN`) with its `hprin` discharged by the
descent step above; the general-`n` form of `exists_gS_three_general`
(`EllipticCurves.FunctionField.PullbackPrincipalityThreeGeneral`) with the tower left abstract.

⚠️ **`[DecidableEq F]` IS bound here and is not bound by the descent step** — `exists_gS_n` binds
it, and `hS` is read over `F` rather than over `N` for the same reason: once the instance is present
the bridge is free. -/
theorem exists_gS_n_of_galois (N : Type*) [Field N]
    [Algebra F N] [FiniteDimensional F N] [IsGalois F N] [DecidableEq N]
    {n : ℕ} (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hcard : Nat.card ((W⁄N).torsion n) = n ^ 2)
    {x y : F} (hns : W.Nonsingular x y) (hS : Point.some x y hns ∈ W.torsion n)
    (hP : ∃ P : (W⁄N).Point, n • P
      = Point.some (algebraMap F N x) (algebraMap F N y)
        ((W.map_nonsingular (algebraMap F N).injective x y).mpr hns)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint hns.left) (n : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n = mulByNEndo n h f :=
  exists_gS_n h hns hS fun _ hf hfdiv =>
    exists_nsmul_divisor_eq_divisor_mulByNEndo_of_galois N h2 hn h hcard hns
      (mem_torsion_baseChange_of_nsmul_eq_zero N hns (mem_torsion_iff.mp hS)) hP hf hfdiv

/-! ## Recovery -/

section Recovery

omit [DecidableEq F] in
/-- **`exists_nsmul_divisor_eq_divisor_mulByThreeEndo_of_galois`
(`EllipticCurves.FunctionField.PullbackPrincipalityThreeGeneral`) is a corollary** — its statement
verbatim, `omit` included, proved from the general form. -/
example (N : Type*) [Field N] [Algebra F N] [FiniteDimensional F N] [IsGalois F N] [DecidableEq N]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x y : F}
    (h : W.Nonsingular x y) (hcard : Nat.card ((W⁄N).torsion 3) = 9)
    (hP : ∃ P : (W⁄N).Point, (3 : ℕ) • P
      = Point.some (algebraMap F N x) (algebraMap F N y)
        ((W.map_nonsingular (algebraMap F N).injective x y).mpr h))
    (hx : W.Ψ₃.eval x = 0)
    {f : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ)) :
    ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
      3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f) := by
  have hx' : (W⁄N).Ψ₃.eval (algebraMap F N x) = 0 := by
    rw [show (W⁄N) = W.map (algebraMap F N) from rfl, WeierstrassCurve.map_Ψ₃,
      Polynomial.eval_map_apply, hx, map_zero]
  have hS : Point.some (algebraMap F N x) (algebraMap F N y)
      ((W.map_nonsingular (algebraMap F N).injective x y).mpr h) ∈ (W⁄N).torsion 3 :=
    mem_torsion_three_some_iff'.mpr hx'
  obtain ⟨g₀, hg₀, hdiv⟩ :=
    exists_nsmul_divisor_eq_divisor_mulByNEndo_of_galois (W := W) (n := 3) N h2
      (by exact_mod_cast h3) (transcendental_xCoord_three_nsmul h2 h3)
      (by simpa using hcard) h hS hP hf (by exact_mod_cast hfdiv)
  exact ⟨g₀, hg₀, by rwa [mulByNEndo_three h2 h3] at hdiv⟩

end Recovery

end WeierstrassCurve.Affine
