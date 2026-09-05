# Elliptic curves

A [Lean 4](https://leanprover.github.io/) formalisation project on the arithmetic
of elliptic curves, built on top of [Mathlib](https://github.com/leanprover-community/mathlib4).

## Scope

The aim of this repository is to formalise results about the reduction theory of
elliptic curves over local and global fields, following Silverman's
*The Arithmetic of Elliptic Curves* (GTM 106). The project builds on Mathlib's
existing theory of Weierstrass and elliptic curves
(`Mathlib.AlgebraicGeometry.EllipticCurve.*`).

The two headline targets are:

* **Semi-stable reduction** of elliptic curves.
* The **Néron–Ogg–Shafarevich criterion**: an elliptic curve has good reduction
  if and only if its Tate module is unramified.

Neither is finished, and neither is untouched. The *good ⇒ unramified* direction of
Néron–Ogg–Shafarevich is proved, in the form stated for an abstract complete DVR
(`Reduction/NeronOggShafarevich.lean`); the converse, and the classical local-field
packaging in which inertia is realised inside `Gal(Kᵘʳ/K)`, are open. For semi-stable
reduction, the reduction-type trichotomy, the `j`-invariant criteria and the
potential-good / potential-multiplicative dichotomy are in place (`Reduction/`), but
the theorem itself is not yet assembled.

### What is formalised

The following are developed here, each in the directory named. This list is a
description of the tree, not a completeness claim: most of these are established
under hypotheses that are stated in the relevant module docstrings, and several
hold at small or restricted indices rather than in general.

* **Reduction over a discrete valuation ring** (`Reduction/`) — the reduction map on
  points and its additivity, the kernel of reduction `E₁(K)` and its identification
  with the formal group `Ê(𝔪)`, injectivity on prime-to-`p` torsion, the reduction-type
  trichotomy and the `j`-invariant criteria, base change to a DVR extension, and the
  good ⇒ unramified direction of Néron–Ogg–Shafarevich.
* **The function field `F(W)`, its places and its divisors** (`FunctionField/`) — the
  affine coordinate ring and its normality, divisors and orders of vanishing, the
  degree-zero theorem and the class group, the places of the projective curve, and the
  multiplication-by-`n` and translation-by-a-point pullbacks.
* **The Weil pairing** `eₙ : E[n] × E[n] → μₙ` (`FunctionField/WeilPairing*.lean`) —
  the divisor-theoretic engine that turns a *principal* `n`-th-root divisor into an
  `n`-th root of the pulled-back function is stated at a general `n`
  (`NthRootOfPullback.lean`); principality is not a consequence of `n`-divisibility —
  that gap is exactly what the pairing measures — and the root `g_S` itself is
  constructed at `n = 2` and `n = 3` only, as is everything downstream of it: the
  pairing as a function of two torsion points, its bilinearity, antisymmetry, the
  alternating property, non-degeneracy, perfectness, Galois equivariance and the
  identification of `det ρ_{E,n}` with the cyclotomic character `χₙ`.
* **The Weierstrass formal group** (`FormalGroup/`) — the coordinate series `x(z)`,
  `y(z)`, the formal group law `F_E` as a genuine bivariate power series with its
  commutativity and associativity, the formal logarithm and exponential, the
  multiplication-by-`n` series, and the group `Ê(𝔪)` over a complete local ring.
* **`n`-torsion and division polynomials** (`Torsion/`, `DivisionPolynomial/`) — `E[n]`,
  the duplication and tripling coordinate formulas, surjectivity of `[2]` and `[3]`,
  and the structure theorem `E[n] ≅ (ℤ/nℤ)²`, currently proved for every `3`-smooth `n`
  over an algebraically closed field of characteristic other than `2` and `3`.
* **The Tate module and its Galois representation** (`TateModule/`) — `T_ℓE = lim_k E[ℓᵏ]`,
  the matrix form `ρ_ℓ : G → GL₂(ℤ_ℓ)` of the ℓ-adic representation, its continuity, and
  the profiniteness of its image. `T_ℓE ≅ ℤ_ℓ²` is unconditional at `ℓ = 2` and `ℓ = 3`,
  and at a general `ℓ` it is reduced to a coherent system of generating pairs for the
  `E[ℓᵏ]` (`TateModule/PrimaryFree.lean`).
* Supporting Galois-theoretic material (`Galois/`) and the Newton-polygon dichotomy for a
  Weierstrass equation (`NewtonPolygon.lean`), which is consumed by both `Reduction/` and
  `FunctionField/`.

## Layout

Measured at commit `d5951f8`; the counts drift, the structure does not.

```
EllipticCurves.lean          -- root module, imports the whole library
EllipticCurves/
├── Basic.lean               -- re-exports two Mathlib modules; only EllipticCurves.lean imports it
├── NewtonPolygon.lean       -- the slope-3/2 dichotomy at a pole of a Weierstrass equation
├── DivisionPolynomial/      --   1 file   coprimality of the division polynomials
├── FormalGroup/             --  57 files  the Weierstrass formal group law and Ê(𝔪)
├── FunctionField/           -- 167 files  F(W), its places and divisors; the Weil pairing
├── Galois/                  --   3 files  cyclotomic character, unramified Galois modules
├── Reduction/               --  65 files  reduction over a DVR; reduction types; NOS
├── TateModule/              --  36 files  T_ℓE and the ℓ-adic representation ρ_ℓ
└── Torsion/                 --  29 files  E[n] and the torsion structure theorem
```

360 `.lean` files in total. `FunctionField/` is flat rather than nested; within it the
file-name prefixes `MulByTwo`/`MulByThree`/`MulByN`, `Translation`, `Place`, `Divisor` and
`WeilPairing` are what group the material.

New files should be added under `EllipticCurves/` and imported from the root
`EllipticCurves.lean` module (kept in sync with `lake exe mk_all`).

## Docstring conventions

### Reach clauses

A **reach clause** is a docstring phrase that says how far a named declaration or a named
layer goes — *"at every `3`-smooth `n`"*, *"at every `n` with `(n : F) ≠ 0`"*, *"the same at
every index"*. They are what a reader consults instead of the signature, and on this
development they are the one kind of prose that has repeatedly gone stale in a way no build
can see.

**A reach clause names every hypothesis of the statement it describes, or it names none.**
The defect is the *proper non-empty subset*: naming the index condition and silently dropping
`(2 : F) ≠ 0` reads as a complete hypothesis list, because a clause that lists one condition
looks like a clause that lists them all. Concretely:

```
-- wrong: `card_torsion_eq_sq` also takes `(2 : F) ≠ 0`
`card_torsion_eq_sq` is `#E[n] = n²` at every `n` with `(n : F) ≠ 0`

-- right
`card_torsion_eq_sq` is `#E[n] = n²` at every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`

-- also right: no `with` clause at all, deferring to the signature
`card_torsion_eq_sq` is `#E[n] = n²` at a general index
```

**Some phrases look like reach clauses and are not**, and their number is deliberately not given
(`#1678`), on the precedent `### Scope of the rules above` sets one section down. Each has been
flagged, triaged and cleared more than once, so the discriminators are written down here rather
than re-derived each round. ⚠️ This read *"**Two phrases look like reach clauses and are not.**
Both have been flagged, triaged and cleared more than once"* (`f1d1473`, `#1569`, PR #620),
true from that commit until the third discriminator below was added — a numeral standing over a
list is falsified by whatever next extends the list, which that section states in terms and
answered the same way. ⚠️ **Both numeral-bearing words are quoted, and they are two words rather
than one**: *"Two"* and *"Both"* were written by one commit and either alone would leave the
other with no account of why it changed. The ordinal reference below — *"The second
discriminator"* — is untouched, because it names a **position** and not a count. They are:

* **A phrase that says which indices the statement is a claim *about* is part of naming the
  theorem, not a hypothesis list**; a phrase that enumerates the conditions under which the
  statement holds is. *"Away from the multiples of the least vanishing index, `ψ` does not
  vanish"* (`ψ_evalEval_ne_zero_of_not_dvd`) is the `∀ m, ¬(d ∣ m)` **inside** the conclusion, not
  a restriction on when the theorem applies. Same for `ψ_evalEval_eq_zero_of_dvd`.

  ⚠️ **`divT_add_mul_of_not_dvd` and `divY_add_mul_of_not_dvd` are the same register with that
  quantifier telescoped, and this is why the discriminator is not syntactic.** They bind
  `(j : ℕ) (hj : ¬ ((e + 3) ∣ j))` **explicitly** and conclude `∀ q : ℕ, …`; the conclusion's own
  quantifier is the `∀ q` the headline calls *"at every multiple of the period"*, while the phrase
  cleared here — *"off the multiples of `d`"* — is a binder. A rule keyed on which side of the `:`
  the condition sits would clear two of these four sites and convict the other two.

  ⚠️ **And no sharper syntactic rule is available**, so do not write one. `card_torsion_pow_of_odd`
  telescopes identically — `{p : ℕ} (hodd : Odd p) (hp : (p : F) ≠ 0)` *is* `∀ p, Odd p → …` — and
  *"at an odd `p`"* **was** a defect (PR #619). The test that does separate them is to **delete the
  phrase and read what is left.** If the remainder is a statement of the same kind, the phrase was a
  restriction on when it applies and is a reach clause: *"`#E[pᵏ] = (pᵏ)²`"* stands perfectly well
  without *"at an odd `p`"*, and `card_torsion_eq_sq` is that statement. If the remainder is no
  longer the theorem, the phrase was part of the predicate: *"`ψ` does not vanish"* without *"away
  from the multiples of the least vanishing index"* is contradicted by the declaration immediately
  below it, `ψ_evalEval_eq_zero_of_dvd`, and *"the predicted `ψ₂`-value is periodic with period
  `d`"* without *"off the multiples of `d`"* is not what `divT_add_mul_of_not_dvd` proves —
  `divT_add_of_not_dvd`, the single step it iterates, asks `¬ (d ∣ j)` at every rung.

  ⚠️ **The test asks whether the remainder is a claim of the same kind, not whether it is still
  true.** **Every** reach clause leaves something false when it is deleted — that is what *"the
  conditions under which the statement holds"* means — so *"the remainder is not true"* holds of
  the entire class and is never on its own a reason to call a phrase part of the predicate. Read
  the second half that way and it clears `card_torsion_pow_of_odd`, the declaration the paragraph
  above opens by convicting: `#E[pᵏ] = (pᵏ)²` with nothing attached is false in characteristic `p`
  too, and is nonetheless what *"stands perfectly well"* means. Both halves are already carrying
  that distinction in their citations — `card_torsion_eq_sq` **is** `#E[pᵏ] = (pᵏ)²` under a
  different condition, while `ψ_evalEval_eq_zero_of_dvd` proves the **opposite** on exactly the set
  *"away from the multiples of the least vanishing index"* removes — so read what the tree proves
  beside a row before deleting anything in its headline.

  ⚠️ **On a row this bullet does not already decide by name, the truth-reading inverts, and it
  reached a confirmed proper-subset defect.** *"as soon as `e_2(P, T) ≠ 1`"*
  (`intCast_eq_zero_of_zsmul_add_zsmul_eq_zero_two`,
  `EllipticCurves.FunctionField.WeilPairingDeterminant`) also leaves something false when deleted,
  so a truth-reading calls it predicate; the headline was then left with no reach clause at all and
  the row landed **cleared** on the *"or it names none"* branch. It is not the case of the four
  sites above: nothing in that file proves anything on the set the phrase removes, and *"`P` and
  `T` are `ℤ/2`-independent"* is the same claim about the same `P` and `T` with the phrase saying
  when it holds. So it is a reach clause; the statement also binds `(2 : F) ≠ 0`, and the headline
  **named it nowhere**. `…_three` is the identical shape. Neither was repaired by this clause — it
  only stopped the test from clearing them, and PR #631 (`#1576`) then repaired both: the headlines
  now read *"over a field with `(2 : F) ≠ 0`, as soon as `e_2(P, T) ≠ 1`"* and *"over a field with
  `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, as soon as `e_3(P, T) ≠ 1`"*, so the *"or it names none"*
  escape went with them. ⚠️ **The classification is what this paragraph is for and the repair
  does not touch it**: the phrase is a reach clause because of what the file proves beside it, not
  because the row was defective, and a row repaired on that reading is evidence the reading was
  right.
  ⚠️ **A clause that restricts the POINT or the PLACE rather than the index is decided by this same
  test, and the answer is not uniform across a case split** (`#1728`). *"at an affine point that is
  not `n`-torsion"*, *"at every affine `P` that is not `n`-torsion"*, *"at every affine `n`-torsion
  point"* and *"every affine `n`-torsion place"* are one clause in four wordings, carried by the
  **six** rows of `EllipticCurves.FunctionField.MulByNFibre`'s *"### The contraction at a rational
  point, at every `n` with `((n : ℤ) : F) ≠ 0`"* section that carry one at all — ⚠️ **not** the
  shorter *"### The contraction at a rational point"* section above it, which is a different
  four-row section and is what a grep for the short title finds first —
  `ord_mulByNCoordHom_XClass_pos`, `ord_mulByNCoordHom_YClass_pos`,
  `ord_mulByNEndo_genX_nonneg`, `comapProjPointN_pointClosedPoint_of_ΨSq_ne_zero`,
  `ord_mulByNEndo_genX_neg` and `comapProjPointN_pointClosedPoint_of_eval_ΨSq_eq_zero` — and the
  test sorts them **five to one**. Ask what the tree proves with the clause struck out:
  * **Some declaration states the same conclusion with the case hypothesis gone.** Then the split
    is an artefact of the proof, the clause says when *this row* applies, and it is a reach clause
    owing the rest of the list. `comapProjPointN_pointClosedPoint_of_ΨSq_ne_zero` is the one row
    here on this side: strike its clause and what is left — *"`[n]` on places is `[n]` on points"* —
    is `comapProjPointN_projPointOfPoint_of_ne_zero`, the assembly that section is built around,
    whose docstring names this row as one of the three **branches** it puts together.
  * **No declaration does.** Then the clause is part of the predicate and the headline is on the
    *"or it names none"* branch. Either a sibling proves the **opposite** on exactly the set the
    clause removes — `ord_mulByNEndo_genX_nonneg` (*"`x ∘ [n]` is regular …"*) and
    `ord_mulByNEndo_genX_neg` (*"… has a pole …"*) are the `ψ_evalEval_ne_zero_of_not_dvd` /
    `ψ_evalEval_eq_zero_of_dvd` pair above transposed, eighty lines apart and split on the same
    `ΨSqₙ(x) ≠ 0`, and `comapProjPointN_pointClosedPoint_of_eval_ΨSq_eq_zero` is contradicted on
    its own removed set by the branch beside it — or the conclusion is not **formable** at all off
    the clause, which is the
    two `ord_mulByNCoordHom_*_pos` rows: `x(n • P)` is `Φₙ(x)/ΨSqₙ(x)`, and at an `n`-torsion `P`
    there is nothing for the headline to say vanishes.

  ⚠️ **Decide this only when you are about to CLEAR a row, never when you are about to complete
  one.** An insertion is branch-neutral: it moves a headline from *"or it names none"* to *"names
  every hypothesis"*, and both branches are compliant, so appending the missing conditions is right
  whichever way the call goes. That is what makes `fddba5c`'s four `ord_*` repairs (`#1664`,
  PR #684) correct under the ruling above even though it puts all four on the predicate side, and
  it is why nothing here reopens them — `### Scope of the rules above`'s *"clearing this one would
  have left the block with rows in two registers"* is an independent ground for them in any case. A
  **clearance** is the one move that turns on the headline having no reach clause at all, and it is
  the only move that has to pay for this call.

  ⚠️ **The `n = 2` and `n = 3` ancestors of the convicted row were convicted with it, and are named
  rather than counted.** `comapProjPointTwo_pointClosedPoint`
  (`EllipticCurves.FunctionField.MulByTwoFibreAffine`) and `comapProjPointThree_pointClosedPoint`
  (`EllipticCurves.FunctionField.MulByThreeFibre`) carry the same clause on the same generic
  branch — each is the generic case of an assembly that states the conclusion unrestricted — and
  all three headlines now name their conditions (`#1735`): *"…at an affine non-`2`-torsion point,
  with `(2 : F) ≠ 0`"*, *"…at an affine non-`3`-torsion point, with `(2 : F) ≠ 0` and
  `(3 : F) ≠ 0`"*, and at general `n` the wording of the four `ord_*` rows beside it.
  ⚠️ This read *"neither headline names `h2`, nor, at `n = 3`, `h3`"*, with a second ⚠️ adding that
  both answered it in a *"No hypothesis on `F` beyond …"* sentence **lower in the same docstring**,
  which `### Scope of the rules above` rules does not repair a headline (`0a1049f`, `#1728`,
  PR #688) — true when written and false from the repair on both counts, since those two sentences
  were re-scoped to the `[W.IsElliptic]` contrast they also carry, which is the half no headline
  here states. ⚠️ **The conviction itself is not retired and is what the repair discharged**: an
  insertion is branch-neutral, so a repaired row is evidence for the reading that convicted it and
  never against it, which is what this bullet already says in terms of
  `intCast_eq_zero_of_zsmul_add_zsmul_eq_zero_two` and `…_three` above. Their
  two `_of_eval_…_eq_zero` siblings are cleared with `MulByNFibre`'s. ⚠️ **The tree-wide population
  of point-and-place clauses is much larger and is deliberately not counted here**, on this
  section's own precedent: a first-pass recogniser returns over a hundred headlines and is already
  known to miss rows on a backtick boundary, so measuring it is `#1137`'s, and the three convicted
  rows named above — one at general `n`, one at `n = 2`, one at `n = 3` — were filed with it as
  `#1735` rather than swept here, and repaired under that issue.
* **A phrase about a fixed numeral is a remark, not a reach clause.** *"`#E[10] = 100`, at an index
  that is neither odd nor `3`-smooth"* (`card_torsion_ten`) cannot be a hypothesis list, because
  `10` is not quantified and there is nothing for a condition to range over. Same for
  `nonempty_torsionThirtySix_addEquiv`, `card_torsion_four`, `nonempty_torsionFour_addEquiv` and
  `nonempty_torsionTwelve_addEquiv`.
* **A phrase that says which declaration this one generalises is provenance, not a reach clause**
  (`#1678`). *"The general-`n` form of `X`"* names a **lineage** — this declaration is the
  general-`n` layer's version of the numeral-indexed `X` — and answers *which merged declaration
  this generalises*, not *which indices this reaches*.
  ⚠️ **The deletion test above does not decide this class, which is why it needs a bullet of its
  own.** Delete *"the general-`n` form of `mulByTwoCoordHom_injective`"* from
  `mulByNCoordHom_injective`'s headline and the remainder — *"Dominance for `mulByNCoordHom`"* —
  is a claim of the same kind, so the test returns **reach clause**, wrongly. That test sorts
  *predicate* from *reach*, and provenance is a third thing neither of its branches has room for.
  What does decide it is `### Scope of the rules above`'s *"**The subject decides, not the
  string**"*: a reach clause's subject is this declaration and its predicate is a set of indices,
  while this phrase's subject is the **pair** of declarations and its predicate is a relation
  between them.
  ⚠️ **The wide reading is refuted by the tree rather than merely unattractive.** Measured at
  `8d31527` with a nesting-aware `/-`-depth extractor over every `EllipticCurves/**/*.lean`,
  whitespace-normalised and `**`-stripped, matching ``the general-`n` forms? of``
  **case-insensitively** — ⚠️ **the case matters and is not a detail**: this tree writes both
  *"The general-`n` form of"* at the head of a headline and *"the general-`n` form of"* mid
  sentence, and either anchoring alone splits the class rather than measuring it — lowercase
  `the` returns **23**, capital `The` **33**, and only the two together are the 56. The phrase
  occurs **56** times — **43** in `/--` headlines, **13** in `/-!` module blocks — and
  **29** of the 43 head a declaration binding a condition on the index: `n ≠ 0`, `(n : F) ≠ 0`,
  `((n : ℤ) : F) ≠ 0`, `3`-smoothness of `n`, or the instance `[NeZero n]` — **28** if that
  instance is not counted, and one of the 29 (`divisorProj_mulByNEndoOfAlgClosed`) takes `n ≠ 0`
  from a `variable` line and not from its own binder list, so the count is over the binders **in
  scope** and not over the ones written at the declaration.
  ⚠️ **The non-constancy hypothesis is not a condition on the index, and the other 14 rows are
  not convicted by carrying one.** Thirteen of them bind
  `Transcendental F (n • genericPoint …).xCoord` and nothing else about `n` — three of those add
  an `n`-torsion condition on a *point*, which is a condition on the pair and not on the index —
  and `fixedFieldN` binds nothing about the index at all.
  `EllipticCurves.FunctionField.WeilPairingGaloisRootN` rules exactly this of its own brick, whose
  *"at every `n`"* stands beside the non-constancy and is true. ⚠️ **A binder NAME decides
  nothing**: this tree writes the non-constancy as `hn` as readily as `hT` or `h`, so a recogniser
  keyed on the name `hn` sorts `functionFieldMap_mulByNEndo` and `mulByNCoordHom_injective` — the
  same hypothesis over the same reach, one named `hn` and one `hT` — onto opposite sides, and
  convicts the brick (`#1678`). Read as a reach clause the phrase tells the reader those 29 reach
  *the general* indices, which is **false** rather than partial, and this
  section treats false the more severely of the two. **29** of the 43 also state an index range in
  the same headline — ⚠️ **a different 29**: this one is measured on headline text and the first
  on the binders in scope, and neither set contains the other. ⚠️ **Only one direction of that is
  witnessed by name here, and the asymmetry is the point**: **four** rows state a range and bind no
  index condition — `galoisFunctionField_mulByNEndo`, `functionFieldMap_mulByNEndo`,
  `weilPairingElt_divisorSlot_add_n` and `weilPairingElt_pow_eq_one_of_gS_n_torsion` — and stating
  a range a signature does not ask for is nobody's sweep, so those four are durable — both
  figures on the recogniser published below. The other
  direction is the **witness slot** measured further down this bullet, and it is named there under
  a date rather than here under a present tense (`#1728`) —
  **24** of them a range
  strictly narrower than every `n`, so the wide
  reading has those headlines answering one question twice and incompatibly:
  `torsionNMulGaloisEquiv_of_ne_zero` (`EllipticCurves.FunctionField.MulByNGaloisGroup`) reads
  *"at every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0` … the general-`n` form of
  `torsionNMulGaloisEquiv`"*, and `card_torsionNMul`
  (`EllipticCurves.FunctionField.TranslationActionN`) *"at every `3`-smooth `n ≠ 0` with
  `(2 : F) ≠ 0` and `(3 : F) ≠ 0` … the general-`n` form of `card_torsionThreeMul`"*.
  ⚠️ **That second witness used to be `ord_mulByNEndo_genX_nonneg`, and `#1664` falsified it
  twenty-three minutes after this bullet landed** (`#1725`). It read
  *"`ord_mulByNEndo_genX_nonneg` binds `((n : ℤ) : F) ≠ 0` and states none"* (`7f0a162`, `#1678`,
  PR #685); that row's headline now names `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`, as does
  `ord_mulByNEndo_genX_neg` beside it, so both state what they bind and neither witnesses anything.
  ⚠️ **A dated census does not owe a re-measure and this parenthetical did, and the difference is
  the discriminator worth keeping**: `## Layout`'s *"the counts drift, the structure does not"* and
  `### Module-block bullets`' *"Date the answer"* say a **count** under a named head is not
  falsified by a later head. A **present-tense claim about a named declaration** is not a count —
  a reader checks it against the declaration, not against the head — so it is falsified, and
  `### Retired claims` binds on it and not on the figures beside it.
  ⚠️ **The `29` and the `24` are a triage pair and not a measurement**, on the precedent
  `### Module-block bullets` sets two sections down for its own `59`: the recogniser for them is
  the one figure in this bullet never written out, and four implementations of it return **27**,
  **28**, **29** and **30** over the same 43 rows, differing on the phrase list and above all on
  whether a range over *points* — *"at every affine `n`-torsion point"*, *"at an affine point
  that is not `n`-torsion"* — counts as a range over the index. **The two rows named above have
  since crossed onto both sides.** They corroborate and are not the argument: the two examples
  are, and both are still true at head.
  ⚠️ **The witness slot — the rows that bind an index condition and state no range — is published
  with its recogniser** (`#1658`, `#1728`), because that is the one figure the pair above never
  wrote out. Measured at `3e1bef2` over the same 43 rows and the same extractor: a headline states
  an index range if it either **(a)** carries an index-quantifier phrase — ``at every `n` `` (19),
  ``at every `3`-smooth `n ≠ 0` `` (6), *"at every index"* (1), ``at general `n` `` (1),
  ``for every `n ≠ 0` `` (1), and *"at a general index"* / *"at an odd `p`"*, which are declared and
  match nothing in this corpus (0) — or **(b)** carries an inline code span constraining the
  index — `` `n ≠ 0` ``, `` `(n : F) ≠ 0` ``, `` `((n : ℤ) : F) ≠ 0` ``, `` `3`-smooth ``. Headline
  means the block text `**`-stripped and whitespace-normalised, cut at the first `.` followed by
  optional bold, code-span, bracket or quote marks and a space, or at the first ⚠️, whichever comes
  first. That returns **30** stating a range and **13** not — and it is *"or"*, not *"and"*, which
  is where two implementations part: (a) alone returns 28 and
  (b) alone 25, which is the spread the marking above is for and the reason a bare numeral was
  never going to settle it. ⚠️ **Match the (a) phrases as they are written here, condition and
  all.** The corpus writes the index span with its own condition inside it, so the normalised forms
  ``at every `3`-smooth `n` `` and ``for every `n` `` match **zero** rows and drop (a) to **21** —
  whether a quantifier phrase's index span may carry a condition is a **fifth** axis of the spread,
  and it is the one that moves the slot: an (a)-only recogniser reading the normalised forms puts
  **12** rows in it, against the **5** an (a)-only recogniser reading these forms does and the
  **3** the full test below finds.
  ⚠️ **The slot has three rows at `3e1bef2`, and a dated measurement may name what a
  present-tense parenthetical may not:**
  * `comapProjPointN_pointClosedPoint_of_ΨSq_ne_zero`
    (`EllipticCurves.FunctionField.MulByNFibre`) — **short**, convicted by the case-split
    discriminator in the first bullet of this section, `#1137`'s to repair, and it leaves the slot
    when it is repaired — ⚠️ **which `#1735` has since done**, so the count above is the `3e1bef2`
    measurement it says it is and two rows sit here at head. The row's headline now names
    `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`; the entry is kept rather than deleted because the
    measurement is what makes the other two readable as *permanent* occupants and not as a
    remainder.
  * `comapProjPointN_pointClosedPoint_of_eval_ΨSq_eq_zero`, same file — **cleared** by that
    discriminator, so its headline is on the *"or it names none"* branch and no sweep reaches it.
  * `torsion_le_weilPairingPointSubgroup_n`
    (`EllipticCurves.FunctionField.WeilPairingTranslationSlotHprinN`) — binds **only** the instance
    `[NeZero n]`, which *"Instance arguments are ambient"* below exempts in terms, so no sweep
    reaches it either. ⚠️ It is in the binder-**29** and not in the **28**, so it witnesses on one
    of that count's two conventions and not on the other.
  ⚠️ **So the slot is not a subset of the class `#1137` is sweeping, and that is the answer to what
  a witness drawn from a swept population raises** (`#1728`): *states none* is a **compliant
  branch** of this section's rule and not only a symptom of a short clause, so a row can sit in the
  slot permanently, and two of these three do. What made the parenthetical above a countdown was
  not the slot — it was naming a **survivor** in the present tense, which the sweep falsifies the
  moment it arrives and `### Retired claims` then charges for. **Name rows inside a dated
  measurement, where `## Layout`'s *"the counts drift, the structure does not"* protects them; do
  not name in a present-tense parenthetical a row a standing sweep is scheduled to reach.**
  ⚠️ **The qualifier is the rule and not a softening of it**, and the reason is one line up: a name
  is a countdown only when something is scheduled to falsify it. That is why the **four**
  range-stating rows named above keep the present tense — no sweep on this front removes a range
  statement from a headline or adds an index binder to a signature, so nothing is scheduled to
  reach them — and why the slot's three are named under a date instead, the one of those three
  `#1137` is scheduled to reach carrying its own expiry in the sentence that names it. That is the
  ruling `#1728` asked for, and it is
  why the *"and states none"* half of that parenthetical is now a pointer to this paragraph rather
  than a name.
  ⚠️ **Everything else in this bullet is confirmed unmoved at `fddba5c`, not assumed**: `56` /
  `43` / `13`, the `23` / `33` case split, the `132` and the `120` / `113` siblings all re-run to
  the unit, and the binder-measured **29** cannot have moved at all, because every commit from
  `8d31527` to `fddba5c` is **docstring-only** — six `.lean` files touched and their stripped code
  byte-identical, so no signature in the tree changed. ⚠️ **Re-derived again at `3e1bef2`** by a
  fourth extractor (`#1728`), which also returns the binder-**29** with
  `divisorProj_mulByNEndoOfAlgClosed` taking its condition from a `variable` line and the **28**
  once `[NeZero n]` is dropped — so the two figures this bullet does not mark as triage have now
  reproduced across implementations, and the two it does mark have not.
  ⚠️ **The sibling wordings go the same way**, because the ground is the phrase's subject and not
  its noun: ``general-`n` <noun>`` (*"the general-`n` surjectivity"*, *"the general-`n` layer"*)
  and *"at general `n`"* — ``general-`n` (?!forms? of)[a-z]`` and ``at general `n` ``, same
  extractor, same case-insensitivity, **132** and **120** further sites at `8d31527`. The ruling
  clears them, and both recognisers are written out beside their counts so the next census meets
  a **measured** rule rather than inferring the width from this bullet's examples. ⚠️ **The second
  figure is what the case rule costs if it is skipped**: case-sensitively it reads **113**, and
  that is the number a first pass at this issue produced.
  ⚠️ **A row cleared here lands on the *"or it names none"* branch and is not exempt from the
  rule.** If its headline names nothing else, the signature is what the reader is deferred to; if
  it names a proper non-empty subset of the hypotheses it is defective for that reason, and the
  phrase neither repairs it nor makes it worse. ⚠️ **So this ruling clears a *phrase*, not the 43
  rows.** **37** of the 43 head a declaration binding an explicit `Transcendental …` argument, and
  what their headlines say about it is `#1137`'s standing question, decided by each file's own
  transcendence register and untouched here.

⚠️ The second discriminator is what separates *"at an index that is neither odd nor `3`-smooth"*
from *"at an odd `p`"*: the first describes the numeral `10`, while the second restricts a variable.
⚠️ Restricting a variable is **not** on its own what makes a clause a reach clause — *"off the
multiples of `d`"* restricts one too. *"at an odd `p`"* is one because it also fails the deletion
test above: `#E[pᵏ] = (pᵏ)²` is still a claim of the same kind once that phrase is removed, and
`divT`'s periodicity without *"off the multiples of `d`"* is not. ⚠️ *Of the same kind*, not
*still true* — `#E[pᵏ] = (pᵏ)²` bare is false in characteristic `p`, and the ⚠️ opening *"The test
asks whether the remainder is a claim of the same kind"* rules that reading out for every row, this
one included.

The rule is about **explicit** hypotheses. Instance arguments are ambient, are carried by the
module's `variable` block, and are visible in the signature doc-gen renders beside the docstring
— so a reach clause need not list them.

**A phrase that names one instance is a claim about that one instance and commits the clause to
nothing else.** *"over `F̄`"* says `[IsAlgClosed F]` is in the declaration's instance list; *"with
no `[IsAlgClosed F]`"* says it is not. Each is compliant exactly when it is true of the instance it
names, and neither is a partial list, because the list is rendered beside the docstring — the
reader is not consulting the phrase *instead of* the signature, which is what makes a partial
**hypothesis** list a defect. So an instance mention is a defect only when it is **wrong about the
instance it names**, and whether a block mentions one at all is a per-block uniformity question
under `### Scope of the rules above`, not a defect question.

**Name all of them or none binds a phrase that quantifies over the list, not one that names a member
of it.** *"over an arbitrary field"* is a claim about every instance constraining `F` and is held to
all of them: `translateEndo_eq_self_of_mul_algebraMap_cube_eq`
(`EllipticCurves.FunctionField.WeilPairingAlternatingThree`) carries `[Field F]`, `[W.IsElliptic]`
and `[IsDedekindDomain W.CoordinateRing]`; the last two are conditions on the curve and not on `F`,
so the claim holds. ⚠️ A totality phrase stated **relative to a named gate list** —
*"unconditionally"*, *"with no hypothesis left"* — is a gate-discharge claim and is governed by
`### Gate-discharge claims` below, not by this paragraph.

⚠️ **The two directions are not equally safe, and that asymmetry is why any of this is written
down.** doc-gen renders what a declaration *has*, so a presence mention is contradicted on its own
page as soon as it goes stale, while an absence claim is contradicted by nothing a reader can see:
adding one instance to a `variable` line silently falsifies every *"needs no `[…]`"* below it.
`not_forall_det_eq_intCast_of_zsmul_add_zsmul`
(`EllipticCurves.FunctionField.WeilPairingDeterminantLinear`) is the form to copy — it says *"needs
neither `[IsAlgClosed F]` nor `[W.IsElliptic]`"* and records that the `omit` above it is measured
rather than guessed, `unusedSectionVars` having reported both.

⚠️ **The instance list is per declaration, not per `variable` block**, so check it there. `omit
[DecidableEq F] in` removes an instance from the declaration below it, and a declaration may bind
instances the block never had. In `EllipticCurves.FunctionField.MulByNFibre`,
`card_fibre_comapProjPointN_projPointOfPoint_of_ne_zero` and
`fibre_comapProjPointN_eq_range_of_ne_zero` are 24 lines apart with different instance lists, and
`pullbackDivisorN_single_eq_sum_torsion_of_ne_zero` binds `[Fintype (W.torsion n)]` in the
statement. An instrument that reads the `variable` lines and stops gets all three wrong.

⚠️ **This paragraph is not a further discriminator for the bullet list above.** It does not say that
an instance mention looks like a reach clause and is not; it says the reach-clause rule never
reached instances, so there is nothing for the *"or it names none"* branch to decide.

⚠️ **Retired.** PR #613 (`#1137`), which first wrote this paragraph, ended it *"But a clause that
does make an instance claim (with no [IsAlgClosed F]) is making a complete-list claim about
instances, and then the same rule applies to those: name all of them or none."* Read literally that
convicts every headline that names one instance and not the rest —
`card_fibre_comapProjPointN_projPointOfPoint_of_ne_zero`
(`EllipticCurves.FunctionField.MulByNFibre`) says *"over `F̄`"* and carries `[W.IsElliptic]` and
`[IsDedekindDomain W.CoordinateRing]` unnamed beside it. The paragraphs above replace it: a
**mention** is a single-membership claim, and only a phrase quantifying over the list inherits
*name all of them or none*.

Two alternatives were weighed and rejected on a measurement of the tree at `681c146`, where **621**
documented declarations carry `[IsAlgClosed …]` in their effective instance list, **163** name the
closure in the headline, and **45** of the **116** files holding such a declaration are split.
Requiring the mention, and then every instance beside it, moves **458** headlines and needs a policy
for `omit`ted and per-declaration instances; forbidding the mention moves **163** and deletes
*"over `F̄`"* from statements that are false without it. Both replace phrases that are true where
they stand with a rule to be re-derived at every row, and the census found **no headline naming a
closure the declaration does not have** — so on the mention side the class this ruling calls a
defect is, today, empty, and neither alternative would have paid off a single wrong claim.

The rule binds every **explicit** hypothesis, with two narrow exemptions. **The first is
derivability**: a clause may omit a hypothesis that is **derivable from the hypotheses the clause
does name**, since such a hypothesis adds no reach information the clause has not already given.
Where the exemption is used, the derivation is cited once in the module block, so a reader can
check it instead of taking it.

The case this development has is the transcendence parameter of the `[n]∗` layer,
`h : Transcendental F (n • genericPoint).xCoord`, which every statement about `mulByNEndo n h` or
`comapProjPointN n h` carries as an explicit argument:

```
-- right: `h` follows from the two conditions the clause already names, by
-- `transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero` (either cast form)
`fixedFieldN_eq_mulByNFieldRange_of_ne_zero` at every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`

-- wrong: `ramificationIdxN_pos` names no other hypothesis, so `h` is the only thing restricting
-- which `n` are reached, and omitting it reads as unconditional.  It is not: `xCoord_zero` makes
-- `h` false at `n = 0`.
`ramificationIdxN_pos` is `0 < e_p` at every `n`
```

⚠️ **That exemption is about derivability, not about where the hypothesis appears.** A rule keyed
on *"the hypothesis occurs in the conclusion"* would reach `(2 : F) ≠ 0`, which is an explicit
argument of `mulByTwoEndo`, `mulByThreeEndo`, `comapProjPointTwo` and `weilPairingTwo`, and so
occurs inside the conclusion of every statement about them. `(2 : F) ≠ 0` is derivable from nothing
any reach clause on this development names — not from `3`-smoothness, not from `(n : F) ≠ 0` — so it
is reach, and the rule binds it. Omitting it is the defect class `#1137` exists to pay off.

**The second exemption is the non-vanishing of the function a statement is an equation about**, and
it is not the first one in other clothes — `hf : f ≠ 0` is derivable from nothing. A reach clause
answers *where* a statement holds, over which fields and at which indices, because that is the
question a reader settles once and then builds a layer on. A non-vanishing side condition on the
subject function answers *which argument*, and the caller supplying the argument already holds the
answer. `divisorProj_mulByNEndo` (`EllipticCurves.FunctionField.MulByNPlacePullback`) binds
`hf : f ≠ 0`, and its headline names the index condition and not it; that is not the
`card_torsion_eq_sq` defect, because `f` is neither a field nor an index and no layer is built on
the set of `f` at which the identity holds.

⚠️ **The discriminator is what the condition is *about*, and it is NOT *"the binder occurs in the
conclusion"* — the paragraph immediately above rules that test out by name and this one does not
reinstate it.** The two are easy to confuse, because a non-vanishing does typically occur in the
conclusion: `torsion_le_weilPairingPointSubgroup_two`
(`EllipticCurves.FunctionField.WeilPairingTranslationSlotHom`) concludes
`W.torsion 2 ≤ weilPairingPointSubgroup hg 2`. But so does `(2 : F) ≠ 0`, in every statement about
`mulByTwoEndo h2` or `mulByNEndoOfAlgClosed h2 hn` — `divisorProj_mulByNEndoOfAlgClosed`
(`…MulByNPlacePullback`) concludes an equation whose **both sides** take `h2`, and it is a row
PR #637 (`#1605`) repaired on exactly this axis. An occurrence test would clear it and reverse that
repair. What separates them is subject matter: `(2 : F) ≠ 0` restricts the field the statement is
over, `f ≠ 0` restricts the argument its caller passes in.

⚠️ **That discriminator is the whole of the *data-argument* clearance too, and `#1631` is what it
cost to find that out.** `### Module-block bullets` below clears a binder that is *"a data argument
of the object the bullet is about"*, and gives the test as *"does not typecheck without it"*. That
is an occurrence test — the one the paragraph above rules out by name and this one says it does not
reinstate — and read as written it clears `(2 : F) ≠ 0` in every statement about `mulByTwoEndo h2`
or `mulByNEndoOfAlgClosed h2 hn`, which is the occurrence reading the paragraph above says *"would
clear it and reverse that repair"* of PR #637 (`#1605`). **The clearance is real; that wording of it
is not.** What clears a binder is the same thing that clears `f ≠ 0`: the condition is about the
argument the caller passes in — a supplied root, a certificate, a point on the curve. Being an
explicit argument of the object the statement is about is **necessary and nowhere near sufficient**,
because the field and the index reach the conclusion that way too.

⚠️ **So a binder that reaches the object only through a projection is a data argument, and the
projection was never the deciding feature.** `#1631` asked whether `h : W.Nonsingular xT yT`, which
`pointClosedPoint h.left` receives as `h.left` rather than as `h`, clears where a signature binding
`W.Equation x y` outright would. It does, and for a reason that never looks at the application node:
`W.Nonsingular xT yT` is a condition on the point the caller passes in, and it is that whether the
conclusion takes `h`, `h.left`, or a term derived from `h` any other way.
`WeilPairingGaloisRootN`'s `exists_weilPairingElt_galois_of_smooth_of_hprin` and
`exists_weilPairingMu_galois_of_smooth_of_hprin` — one file, one slot, one binding the `Equation`
and the other the `Nonsingular` — are **one case**, and a test that splits them is reporting the
shape of a signature rather than the reach of a clause.

⚠️ **And no narrowing of the occurrence reading rescues it, because this pair is identical on every
feature such a test can see:**

```
theorem residueDegreeN_none_eq_one (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) :
    residueDegreeN n hn (none : ProjPoint W) = 1

theorem ramificationIdxN_pos (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) (p : ProjPoint W) :
    0 < ramificationIdxN n hn p
```

Same binder, same explicit-argument position in the conclusion, the same *"at every `n`"* clause
naming nothing else. This section convicts the second by name above; `### Module-block bullets`
**used to clear** the first by name below, on the data-argument ground this section withdraws — at
`5c3fce2^` that section read *"it is compliant for the other reason, that the declaration's one
propositional binder is a data argument of the object the bullet is about"*. ⚠️ **The opposition is
this argument's premise, and it belongs in the past tense**: PR #651 withdrew the ground, rewrote
that section and wrote this sentence in **one** diff, so *"clears the first by name below"* was
false at the commit that wrote it (`#1643`). What the pair is evidence of does not move — the
document *had* decided two rows no such test can tell apart in opposite directions. Under the
discriminator both are **reach** — `hn` is a condition on the index, and `xCoord_zero` makes it
false at `n = 0` — so the second stays convicted and the first is convicted with it. ⚠️ **Neither
is a sweep and neither is repaired here**: the repair of `residueDegreeN_none_eq_one`'s reading
belongs where that reading stands (⚠️ until `#1649` this clause read *"the two readings below are
corrected where they stand"*, promising a repair for each member of the pair and pointing *below*
for a reading this document keeps above, in its own fenced `-- wrong:` row), and the
`residueDegreeN` row itself belongs to `#1616`.

⚠️ **And the first has since been repaired there**, which is where the sentence above put it:
`#1636` (PR #653) named the condition in the row — it now reads *"at every `n` at which `[n]` is
non-constant"* — and `### Module-block bullets` below carries it as a **repaired** row, the
conviction standing and the reading that drew it marked there as retired. ⚠️ **Nor are the two
*"at every `n`"* clauses this pair is argued from alike, and neither of them is a live bullet
today.** `residueDegreeN_none_eq_one`'s was one until PR #653 and is now a retired reading;
`ramificationIdxN_pos`'s never was — the fenced *wrong* row above is written **for** this document,
and that declaration's own bullet (`EllipticCurves.FunctionField.MulByNPlacePullback`) reads
*"`…ramificationIdxN_pos` giving `0 < e_p`"* and carries no reach clause at all. So the pair argues
a **clause form**, which is what the *right*/*wrong* rows above are for; the live row it touched is
repaired, and `ramificationIdxN_pos` had nothing to repair.

**One mechanical backstop is available, and it is worth running before arguing a row.** Where
deleting the binder leaves the statement provable, it constrains nothing and there is no reach for
a clause to misreport. This is the deletion test above run on the binder side, with the **compiler**
deciding instead of a reader: restate the declaration without the binder and build. `ord` and
`ordInfty` carry documented junk values at `0` (`ordInfty_zero`, *"matching the convention
`ord v 0 = 0`"*), so `div (f ∘ [n]) = [n]∗ (div f)` reads `0 = 0` at `f = 0` and
`divisorProj_mulByNEndo`'s `hf` is a convenience of the proof rather than a condition of the
theorem. ⚠️ The backstop is one-directional and never reaches `(2 : F) ≠ 0`, for two reasons at two
kinds of row: where `h2` is a free-standing hypothesis the deleted form elaborates and is **false**
in characteristic `2`, and where it is an argument of `mulByTwoEndo` or `mulByNEndoOfAlgClosed` the
deleted form does not elaborate at all. Either way the restatement does not build, which is what
makes this a backstop rather than a second discriminator.

⚠️ **This exemption stops at a claim that counts hypotheses.** Where the non-vanishing is
load-bearing *and* the docstring makes a gate-discharge or totality claim about the hypothesis
list, `### Gate-discharge claims` below binds and the word still has to have a subject.
`exists_eq_algebraMap_of_divisorProj_nonneg` (`EllipticCurves.FunctionField.ProjectiveDivisor`)
is the row: its conclusion `∃ c ≠ 0, f = algebraMap c` is **false** at `f = 0`, where the no-pole
hypothesis holds, so its `f ≠ 0` is **load-bearing**, this exemption does not reach it, and
`### Gate-discharge claims` governs its headline. The headline **said** *"from the single
hypothesis that `f` has no pole"* over a signature binding `f ≠ 0` as well, and PR #640 (`#1608`)
repaired it together with the module bullet describing the same row; both now read *"for `f ≠ 0`
and from the single **non-negativity** hypothesis"*. ⚠️ **The classification is what this paragraph
is for and the repair does not touch it**: only the quotation is a claim about the row's text, and
it is past tense for that reason.

Measured at `27d4f29`, from the elaborated telescope: **239** documented declarations bind a
`FunctionField`-valued `≠ 0` hypothesis, every one of them in `FunctionField/`, and **225** of their
headlines do not name it. Of the **18** whose headline named some other condition and not it, **10**
are vestigial by the backstop above, **3** are constituents of the object the statement is about
(the supplied root in `weilPairingPointSubgroup hg 2`, and the data argument of a `def`), and **5**
are load-bearing — of which exactly one makes a counting claim and is therefore governed by
`### Gate-discharge claims` below. Naming it in the other seventeen would put a uniform directory
into two registers, which is what `### Scope of the rules above` is for.

**A cited declaration's *name* does not complete the clause that cites it.** *"surjectivity holds
at every nonzero index (`nsmul_surjective_of_two_ne_zero`,
`EllipticCurves.Torsion.TwoTorsionOrder`)"* is short of `(2 : F) ≠ 0`, and the `_of_two_ne_zero`
inside the backticked identifier four words away does not repair it. A reach clause is what a
reader consults *instead of* the signature; an identifier is a name, not a hypothesis list.

⚠️ **The suffix rule this document already has is a *matching* rule, not a substituting one.**
`### Scope of the rules above` says *"`(n : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` are different clauses.
The `_of_natCast_ne_zero` and `_of_intCast_ne_zero` suffixes say which, and a reach clause should
match the suffix."* That lets a suffix decide **which** of two conditions a clause that already
names one is naming. It does not let a suffix supply a condition the clause names nowhere, and the
two are not points on a spectrum: the defect this section defines is the **proper non-empty
subset**, and a clause that lists the index and drops `(2 : F) ≠ 0` reads as a complete hypothesis
list however the cited identifier is spelled.

⚠️ **Three further grounds, each decisive on its own.**

* The rule would be keyed on **naming luck**. It clears `nsmul_surjective_of_two_ne_zero` and
  clears nothing for `card_torsion_eq_sq`, which binds the identical `h2` and carries no suffix —
  so one block would hold rows in two registers for a reason that is not about the mathematics,
  which is what `### Scope of the rules above` exists to forbid.
* The suffix is **itself a proper subset**. `_of_two_ne_zero` names `h2` and not the `hn : n ≠ 0`
  beside it, so a reader told to read identifiers as hypothesis lists is reading a partial one.
* The development **already writes the compliant form** for this declaration in this phrasing —
  *"`[n]`-surjectivity at every `n ≠ 0` with `(2 : F) ≠ 0`"*
  (`EllipticCurves.TateModule.DeterminantModSmooth`). **12** sentences in the tree named both
  conditions before `#1659`, measured at `5dfd94d` with the recogniser published on that issue. If
  the suffix cleared, all twelve would be redundant and somebody would have deleted them.

⚠️ **This rules on citations, which is the layer no register reaches.** A reach clause about a
declaration whose file the writer is not editing is covered by no register in either file, and no
review of the defining module ever looks at it; the trigger for it going stale is an edit somewhere
else. It is bound by this section exactly as a headline or a `## Main *` bullet is, and the repair
is the one this section already prescribes: name the condition in the clause, or name none.

**A clause that points at another list is a third branch, and it is exactly as complete as the
list it points at.** *"under the same hypotheses"*, *"at the same hypotheses"*, *"with it"*,
*"under the hypotheses of `X`"* name neither every hypothesis nor none: they **incorporate** a list
by reference, so the rule above binds them through their antecedent. A short antecedent is a defect
at every clause pointing at it, in every file, and it is invisible where it lands, because the
pointing clause contains no hypothesis to be missing. ⚠️ Read the antecedent, and read it **for the
anaphor's own subject** — two declarations in one sentence need not share a list, since a condition
may be a binder of one and sit inside the other's predicate. `hasXCoordFormula_of_two_ne_zero`
carries `ΨSqₙ(x) ≠ 0` inside `HasXCoordFormula` while `nsmul_eq_some_omegaY_of_ΨSq_ne_zero` binds
it, and `EllipticCurves.Torsion.Collinearity`'s six words were complete for the first and short for
the second at once. **Where the antecedent is what is short, repair the antecedent**: one insertion
pays off two sentences and stops the propagation.

⚠️ **An anaphor can also fail by importing too much, and that direction is the one nothing
renders.** `neronOggShafarevich_galoisRepMod_eq_one`
(`EllipticCurves.Reduction.NeronOggShafarevich`) said *"under the same hypotheses"* over an
antecedent headline reading *"`ℓ` is a prime invertible in `A`"* — **prime** — and binds no
`[Fact ℓ.Prime]`: a correct instance **mention** was carried across a declaration boundary onto a
declaration that does not have the instance, where it is wrong about the instance it names. The
paragraphs above make a stale mention a defect exactly there, and the asymmetry they rest on is
what makes this shape worse than a stale mention in place — doc-gen contradicts a wrong mention on
its own declaration's page, and cannot contradict one imported from another's.

**Identity is measured on reach, not on the telescope.** *"X has the same hypotheses as Y"* is a
reach clause whenever it is doing reach work, and what it is held to is whether the two are claims
about the same situations, not whether their binder lists match token for token. Two consequences,
each of which decides a row this section would otherwise leave undecidable:

* a binder cleared by the derivability exemption above does not count against it.
  `isGalois_mulByNFieldRange_of_smooth`'s *"the separable half is `#1219`'s
  `isSeparable_mulByNFieldRange_of_smooth`, at the same hypotheses"* is **complete** — the two bind
  the identical five arguments and the transcendence `h` neither names is the exempt one, cited in
  `EllipticCurves.FunctionField.MulByNGalois`'s own transcendence section;
* a residual binder at a fixed numeral restricts nothing, by the *"a phrase about a fixed numeral
  is a remark"* discriminator above. `finrank_torsion_of_smooth h2 h3 (n := 3)` *"has the same
  hypotheses as the merged `finrank_torsion_three`"*
  (`EllipticCurves.TateModule.DeterminantModSmooth`) is **true** although `1 < 3` and `hfac` are
  still binders of the applied term, and `EllipticCurves.FunctionField.MulByThreeGalois`'s *"the
  general-`n` package carries the same hypotheses as this file's at `n = 3` and no fewer"* is true
  for the same reason — `isGalois_mulByNFieldRange_three` certifies it, over `h2` and `h3` alone.

⚠️ **An anaphor is a pointer and not evidence of completeness, so a census may not clear a row on
one.** `#1679` publishes ``under the same hypotheses`` and ``with it`` as **field seeds**, which
clears a row on the strength of a neighbouring list without checking that list is complete for the
new subject. That is sound only where the antecedent has been read: on the `h2` axis it has been,
and `EllipticCurves.TateModule.Profinite`'s *"`card_torsion_le_sq` there proves `#E[n] ≤ n²` under
the same hypotheses"* is the correct row it protects. On any other axis a seeded row is
**unmeasured, not clean** — `Collinearity` above was cleared by that seed on the `h2` axis,
correctly, and was short on the `hΨ` axis in the same six words. The class is small enough that
reading it is the instrument: **25** bare anaphors in **18** files at `4148f23`, out of **32**
occurrences of the phrase family in **23** files, from **231** seeded occurrences in **123** files,
every one read; the seeds and the row-by-row verdicts are on `#1705`.

⚠️ **A clause that points *and* names is not on this branch**, which is what separates those two
counts. *"with the same hypothesis `ΨSqₙ(x) ≠ 0` that … `hasXCoordFormula_of_two_ne_zero` asks of
the `x`-half"* (`EllipticCurves.Torsion.NsmulYPeriodic`) and *"at **every** prime `p` with
`(2 : F) ≠ 0` and `(p : F) ≠ 0` — the same pair as the display above"*
(`EllipticCurves.Torsion.StructureGeneral`) are ordinary reach clauses with an attribution
attached: they carry their own list, so the paragraphs above measure them directly and nothing has
to be resolved elsewhere. The branch is for the clause that points **instead of** naming.

⚠️ **Completing such a clause does not retire anything.** *"at every nonzero index"* is not
falsified by *"at every nonzero index with `(2 : F) ≠ 0`"* — the words stay and a condition is
added — so `### Retired claims` does not bind, and `#1659` added no marked quotation at any of its
sites for that reason. ⚠️ Contrast `#1660`, where *"at every `n`"* over a binder
`xCoord_zero` falsifies at `n = 0` **was** false and each replacement was quoted and attributed.
**Read whether the old clause was false or merely partial before deciding.**

### Gate-discharge claims

A third exemption is narrower still, and it has a different shape: it is not about which
hypotheses a clause omits but about **what kind of claim the clause is making**.

A **gate-discharge claim** says that a statement is owed *nothing further* — *"with `#E[p] = p²`
as the only hypothesis"*, *"with no hypothesis left"*, *"unconditionally"*. It is not a hypothesis
list. It is a claim **relative to a gate list**: the hypotheses that some *other* declaration or
module records as owed, and which this statement has discharged. Read as a reach clause it is a
false universal, and a bolded one; read as what it says it is usually exactly true, and sharper
than the list it would be replaced by.

**A gate-discharge claim is bound by the reach-clause rule only where the gate list it is relative
to is not named.** Where the docstring does name it, the claim is compliant and the completeness
obligation *moves*: the naming sentence is then held to the rule the headline was let off, and
must name every explicit hypothesis of the statement.

```
-- right: `nonempty_torsionPow_addEquiv_of_odd` (`EllipticCurves.Torsion.PrimaryTowerOdd`) binds
-- `h2`, `hp : p.Prime`, `hodd`, `hpF`, and its headline names two of the four
**The structure theorem for `E[pᵏ]` at an odd prime `p`, with no hypothesis left.**
This is the signature `EllipticCurves.Torsion.PrimaryTower`'s gate list reduces to once
`card_torsion_eq_sq_of_odd` supplies `hcard`: over an algebraically closed field with
`(2 : F) ≠ 0`, at an odd prime `p` with `(p : F) ≠ 0`, ... is owed nothing further.

-- wrong: `card_torsion_pow_of_odd` read *"at an odd `p`, unconditionally"* over the same field
-- and index hypotheses, and named no gate list.  Its next sentence made a hypothesis-*list*
-- claim instead — *"asks of `p` only that it be odd and nonzero in `F`"*, which is itself short
-- of `h2` — so nothing in the docstring gave the word a subject.
```

The repair there was to **re-scope the word rather than delete it**: *"with `(2 : F) ≠ 0`, at an
odd `p` with `(p : F) ≠ 0`, and with no `hcard`"*. That is the cheapest form of a gate-discharge
claim and the one to prefer — it names the discharged gate **inside** the clause, so it is
compliant on either reading and needs no second sentence to prop it up.

⚠️ **In the same docstring is the whole of the exemption.** *Declaration headlines are reach
clauses too* below is unchanged by it: a `## Hypotheses` section elsewhere in the module does not
repair a partial headline, because doc-gen renders the rest of *this* docstring beside the
headline and the module block nowhere near it.

⚠️ **A gate-discharge register is a per-file object, and a sweep sees per declaration.**
`EllipticCurves.Torsion.PrimaryTowerAlgClosed` runs one from its H1 (*"`#E[p] = p²` is the only
hypothesis left"*) through its module block and down into the declaration headlines, and factors
the field conditions out into a `## What the substitution costs` section of its own, on purpose.
Repairing one headline of such a file in isolation is a worse outcome than repairing none. Before
repairing a headline whose omitted hypothesis is named in a section like that, read the module
block: the decision on offer is about the file, not the row.

⚠️ **And a per-front one: *"the setting"*.** The whole `WeilPairing*` front writes a gate-discharge
claim in the words *"with no hypothesis beyond the setting"*, and `grep` finds no definition of the
term *as such* anywhere in the tree. Read as a hypothesis list the sharpest of them —
`exists_weilPairingElt_mul_swap_eq_one_two`, which binds `(2 : F) ≠ 0` and six point hypotheses —
is a bolded false universal. It is not one. ***"The setting"* is this development's word for a
gate list**, and `EllipticCurves.FunctionField.WeilPairingGaloisRoot` says so in the one sentence
in the tree that comes near a definition:

> *"It is the pairing's own setting — `e_n` is a pairing on `E[n] × E[n]` — and not a gate carried
> in from elsewhere; in exchange the caller supplies no rung-5 data and no `hpow` proof."*

So the setting is the ambient `variable` block, the front's standing characteristic hypotheses,
and **the data the statement is about** — the points, their torsion, and the group relation among
them. What the clause claims is that no **gate** is carried: no `hprin`, no product relation
`hprod`, no caller-supplied root, no rung-4/5 certificate. That is checkable, and the test is one
question of the signature — *does it bind a gate the clause says is gone?*

⚠️ **This is the one exception to *"in the same docstring is the whole of the exemption"* above,
and it is narrow.** *"The setting"* is a term **this document defines**, not prose sitting
elsewhere in the module: a reader who meets a defined term looks it up once and is then equipped
for the whole register, where a reader who meets a partial hypothesis list has no signal that a
completing sentence exists anywhere. That asymmetry is the whole of what earns the exception, so a
phrase a file coins for itself earns nothing here — until a term is defined in this section, it is
module prose and the boundary above applies to it unchanged.

⚠️ **And the completeness obligation does not move to a second sentence here — it moves to the
signature test.** Under *"the naming sentence … must name every explicit hypothesis"* above,
`exists_weilPairingElt_mul_swap_eq_one_two` would still be a defect: its docstring is the headline
plus one ⚠️ about why `R = S ⊕ T` need not be assumed `2`-torsion, and no sentence in it names the
statement's seven explicit hypotheses (the ⚠️ names three binders in passing, inside a remark about
the proof, and never `h2`). What discharges it instead is that the clause is a claim about
**gates** and the signature carries none. The hypothesis count is the signature's job, which is
what the ⚠️ below already says — so for this register the signature test *is* the obligation, and
demanding a naming sentence as well would convict the whole register for not restating what
doc-gen prints beside them.

```
-- right: `exists_weilPairingElt_divisorSlot_add_two` binds `h2` and eight point hypotheses, and
-- no gate — it produces its three roots — so the clause is true of what it is a claim about
Divisor-slot bilinearity at `n = 2`, over `F̄` with no hypothesis beyond the setting.

-- right: `exists_weilPairingElt_divisorSlot_add_of_smooth_of_hprin` does bind `hprin`, and says so
Divisor-slot bilinearity at every `3`-smooth `n ≠ 0`, with `hprin` the only hypothesis beyond the
setting.

-- wrong: the same clause over a signature that still carries `hprin`, `hprod` or a root the
-- caller supplies.  Naming the carried thing is what the compliant form above does.
-- No live instance, and that is the point: the register is self-policing across the whole front,
-- with the word "no" never standing over a signature that carries a gate (measured on `#1571`).
```

⚠️ **It is not a licence to say the signature is short.** *"Beyond the setting"* says nothing about
how many hypotheses a statement has and everything about which gates it does not carry; a reader
who wants the count reads the signature doc-gen prints beside the docstring. A headline that omits
`(2 : F) ≠ 0` while making a plain hypothesis-list claim is not rescued by this paragraph. The
boundary is the `card_torsion_pow_of_odd` one above: the word has to have a subject.

The per-block clause below does not fire *between* the two registers. A gate-discharge claim and a
hypothesis list are different kinds of claim, not two dialects of one, so a block may hold both
provided each row is compliant on its own terms; what it must not hold is two rows making the
**same** kind of claim in different registers.

⚠️ **And *"the setting"* does not reach a clause that makes no gate-discharge claim.** The question
was filed as `#1626` against thirteen `WeilPairing*` module bullets whose reach clauses — *"at every
`3`-smooth `n ≠ 0`"*, *"at every `n` with `((n : ℤ) : F) ≠ 0`"*, *"over an arbitrary field"* — stand
over signatures binding points, their torsion, a halving point and `hprin` besides. The answer is
**no**, on two independent grounds, and it adds no exemption and withdraws none.

* **This exemption is keyed on the kind of claim, not on which hypotheses a clause omits** — the
  paragraph opening this section says exactly that. *"The setting"* supplies the **subject** of a
  gate-discharge word; a clause carrying no such word has no subject to supply, and there is nothing
  for the term to do. That is the asymmetry `### Module-block bullets` below turns on: a
  gate-discharge word *"is visibly relative to something"*, and a bare reach clause carries no
  signal at all. It is *"not a licence to say the signature is short"* read at its own layer, since
  the licence those thirteen rows need is the one that sentence refuses.
* **And on this front there is no such register to read them against.** A nesting-aware comment
  scanner — one that tracks `/-` nesting and tells `/-!` from `/--`, since these files carry later
  `/-! … -/` section blocks, so a line below the module block need not be in a declaration
  docstring — puts every occurrence of *"the setting"* in these seven files inside a declaration
  docstring, with one module block excepted: `WeilPairingAlternatingBaseChangeN`'s, where the phrase
  occurs only in sentences **declining** the register, not declaring one. ⚠️ **No count is written
  here on purpose**: one docstring moves any number, and what carries the argument is that no module
  block on this front **declares** such a register. Under `### Scope of the rules above` a module
  list and the file's headlines are two blocks, and by `### Module-block bullets`' *"the traffic
  runs one way"* a headline repairs no bullet. So a **yes** would have cleared none of the thirteen
  either; the two answers differ only in what they license next.

**Twelve of the thirteen are therefore defects**, and the repair is the `DeterminantModGeneral`
opener `### Module-block bullets` names — one **reach register** at the head of each of the six
lists — not thirteen rewritten bullets. The thirteenth,
`EllipticCurves.FunctionField.WeilPairingTranslationSlotNotInjective`'s *"for **every** `S`, every
rung-5 root and every certificate"*, clears outright and **not on this ruling**:
`not_injective_weilPairingTorsionMuHom_two` binds `h2`, `hgS` and `hu` and nothing else, the clause
names `(2 : F) ≠ 0` itself, and `hgS` and `hu` are conditions on the root and the certificate it
also names, so the residue is empty. ⚠️ **Not** because all three are arguments of
`weilPairingTorsionMuHom_two h2 hgS hu`: `h2` is an argument of it and is reach all the same
(`### Reach clauses`, `#1631`). `…_three` is the same with `h3`. ⚠️ `#1626`'s own table reports that
row as short of `hu` and an anonymous binder; the signature binds no anonymous explicit
propositional binder, and two further rows of that table are joined to
`transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`, which those two bullets **cite** and
are not about. **Re-derive a row before repairing it** — the join is where these tables go wrong,
and a triage set inherited is a triage set unread.

⚠️ **This is the answer PR #643 (`#1619`) already gave one layer up, and the two repairs differ for
a reason stated above.** #643 named `h` and `htors` in two bullets of
`WeilPairingAlternatingBaseChangeN` rather than leaving them to the setting. Those rows say the
conditions they list *"are the whole hypothesis list"* — a **count** — and *"a register says what a
list omits. It cannot make a count true."* So a head-of-list register was unavailable there and
naming in-row was forced. The twelve make **reach** claims, which a register does reach. Two blocks
in different registers on one question is what `### Scope of the rules above` forbids; two kinds of
claim repaired the two ways this document already prescribes is not.

⚠️ **What this does not decide.** *"The data the statement is about"* is a phrase in this section's
description of a **gate list**. It is not a second route to clearing a data hypothesis from a reach
clause: that job belongs to the data-argument clearance in `### Reach clauses` above, which has its
own discriminator — what the condition is about — and which `### Module-block bullets` applies to a
bullet exactly as to a headline. Read as such a route it
would clear `htors`, `hPT`, `hS` and `hm₂`, which no object in any of these conclusions takes, and
it would swallow `(2 : F) ≠ 0`, which `### Reach clauses` names as reach in terms. ⚠️ Nor does it
settle whether a binder reaching the conclusion only through a **projection**
(`pointClosedPoint h.left` over `h : W.Nonsingular xT yT`) is a data argument: it was one on this
document's plain words and not one under the direct-argument mechanisation, and the two split
`exists_weilPairingElt_galois_of_smooth_of_hprin` from its `Mu` twin in the same file — the first
binds the `Equation` and the second the `Nonsingular`. ⚠️ **Neither reading changes the verdict on
any of the twelve** — each keeps `hprin`, a torsion hypothesis or
`(2 : F) ≠ 0` in its residue on both. It was filed as `#1631` and is answered in
`### Reach clauses` above rather than here — a condition on the point the caller passes in is a data
argument however the conclusion reaches it — so what those registers must name is settled, and it is
not settled by this section.

### Module-block bullets

A `## Main statements` / `## Main results` bullet makes the same kind of claim, about the same
declaration, as that declaration's headline does. The two registers above therefore reach it, and
`### Scope of the rules above` below scopes this section as it scopes them — but the reader is in a
different position, and one clause of that section, *"Declaration headlines are reach clauses too"*,
**inverts** here.

**A bullet is read inside its own list.** *"Declaration headlines are reach clauses too"* is
justified by rendering distance: doc-gen prints the rest of *this* docstring beside a headline and
the module block nowhere near it, so a completing sentence in the module block is one the reader of
a headline never sees. At the module-block layer that distance is zero — a bullet's context *is* the
block, contiguously above it. So a **register** — a sentence in the block that says what the bullets
under it leave out — can reach a bullet in a way that the same sentence could never reach a
headline, and such a bullet is compliant relative to it.

⚠️ **How far it reaches depends on which of the two registers above the bullet is answerable to,
and the two scopes are not the same.** This is the whole of the reading, and getting it wrong in
either direction decides a different population.

* A **reach register** names the hypotheses its bullets omit. It binds **the list it heads** and
  nothing further up the docstring. The tree writes these —
  `EllipticCurves.FunctionField.MulByNFibre` (*"**Every one of the thirteen below does take
  both**"*, scoped inside a bullet) and
  `EllipticCurves.TateModule.DeterminantModGeneral`, whose `## Main statements` **opens** *"**Every
  statement and definition below takes `(2 : F) ≠ 0` and `(n : F) ≠ 0`**, and the rank and the basis
  take `1 < n` as well; the bullets give the conclusions and not the hypotheses"*.
  ⚠️ **`DeterminantModGeneral`'s closing clause is not the form to copy, and it is the last live
  instance of it in the tree.** *"The bullets give the conclusions and not the hypotheses"* is a
  **universal over the bullets**, which `#1647` decided against — as a **form**, and separately
  from whether it is true of any particular list. That quotation is not edited here: what this
  section prescribes is the **naming** half of the sentence, and the closing form to copy is below.
  ⚠️ **`MulByNFibre` closed on the same clause until `#1686` and no longer does**, which is why
  only its naming half is quoted: its universal was false of the thirteen on the day it landed, two
  of the rows naming the binders their declarations bind. `DeterminantModGeneral`'s list was read
  row by row and its universal **holds**, which is why it is left standing.
* A **gate-discharge register** supplies the *subject* of *"unconditionally"*, *"with no hypothesis
  left"*, *"nothing further"* — the gate list the word is a delta against. It may sit **anywhere in
  the module block**. `### Gate-discharge claims` above already treats such a register as a
  per-file object and names the precedent, `EllipticCurves.Torsion.PrimaryTowerAlgClosed`, which
  runs one from its H1 through its module block and down into the declaration headlines.

⚠️ **The asymmetry is not new either — it is the one `### Gate-discharge claims` states, with the
unit moved.** That section earns its exception on the ground that *"a reader who meets a defined
term looks it up once and is then equipped for the whole register, where a reader who meets a
partial hypothesis list has no signal that a completing sentence exists anywhere"*. A
gate-discharge word carries that signal — it is visibly relative to something — so a subject
anywhere on the page it is printed on will do. A partial reach clause carries no signal at all, so
the register has to be where the reader meets it, and a paragraph two `##` sections up is the
*"prose sitting elsewhere in the module"* the boundary excludes. What this section contributes is
therefore the **reach** half; the gate-discharge half follows from the rule above once the unit is
the module docstring.

⚠️ **How far above its list a reach register may sit, in terms, because the two sentences above
name two different units and both call theirs *"the block"*** (`#1668`). *"It binds the list it
heads"* and *"a bullet's context **is** the block, contiguously above it"* are consistent read
each against its own unit and inconsistent read against the other's; what settles it is that the
two registers do not share a unit, and this document already fixes both:

* a **reach register**'s unit is **its list**. That is the `## Main *` section it opens, or a
  sub-list inside one: it begins at that heading and ends at the next heading of the same or a
  higher level, and the register binds the bullets **below** it inside that span and nothing else.
  `### Scope of the rules above` is where the unit is written down — *"a `## Main statements` list
  … is one place"* — so *"the block"* in *"a bullet's context is the block"* is that list.
* a **gate-discharge register**'s unit is the **module docstring**, which is what *"anywhere in the
  module block"* says, and `MulByNResidueDegree`'s worked example below is a subject sitting two
  `##` sections above the list it serves.

⚠️ **So prose in another `##` section does not clear a bullet, and the distance does not enter.**
*"A paragraph two `##` sections up"* above is the instance the boundary was stated on, not the
boundary: **one** section up is excluded on the same ground, and so is one paragraph up on the
other side of a heading. ⚠️ **Nor does a register reach a bullet *above* it** — that is the
*"nothing further up the docstring"* half read in the other direction, and it is what makes a
sub-list's register invisible to the outer list, as the *"Not reached"* row below records.

⚠️ **This narrows nothing and retires nothing.** Each wording was true of the unit it governs, so
`### Reach clauses`' *"was the old clause false or merely partial"* test puts this paragraph under
**completing** a clause, and `### Retired claims` says completing retires nothing. What is new is
that the two units are named beside each other, which is the whole of what `#1668` asked for.

⚠️ **And it points the same way as *"Nor does a sentence lower in the declaration's own
docstring"*** in `### Scope of the rules above` (`#1660`), which is the reconciliation that decides
this rather than the wording. That ruling holds a completing sentence **four lines** from its
headline insufficient, on the ground that the reader meets the clause first and a partial one
carries no signal. A register in another `##` section is fifty lines from its bullet. The two
rulings differ in **unit** — a headline is its own unit, a bullet's unit is its list — and give the
same answer for the same reason; a rule that let a bullet reach further than a headline would have
to say why, and there is no ground for it.

⚠️ **A sentence that cites the derivability exemption is not thereby a register**, and calling it
one is a label rather than a reach claim — which is what the convicted population turns on.
`EllipticCurves.FunctionField.MulByNGalois`, `…MulByNGaloisGroup` and `…MulByNPlaceComposition`
each open a `## ⚠️ The transcendence parameter` section with the same sentence, and
`…MulByNComposition` carries it under `## Hypotheses, and the one that has to be composed first`;
all four say **in the next clause** that the exemption is what clears their rows, so no bullet of
theirs hangs on the label. `…MulByNInertia` said *"cleared by the register and not by the
exemption"* of three declarations, which is a clearance stated **on** the register, and is what
this ruling convicts.

**Measured at `8d31527`, with the recogniser written out, as this section requires.** Over every
`/-! … -/` block of every `git ls-files '*.lean'`, lines matching `\bregister\b`, or matching
`(every|all|each).*(below|above).*(takes?|binds?|carr(y|ies)|is stated|is an)`
**case-insensitively**, keyed to the `## ` section they sit in — **150** lines in **68** files,
read one by one.

⚠️ **The universal alternative is loose on three axes on purpose, and every one of the three was
found by losing rows to it.** It is **unanchored**, because this tree writes *"Everything below
carries …"* as a third wording of the same object and `\b(Every|All|Each)\b` drops every one of
them; it is **case-insensitive**, because the same universal is also written mid-sentence in lower
case — `…FunctionField.MulByNComposition`'s *"so every statement below takes the hypothesis as an
ordinary argument"*, `…TateModule.FreeGeneral`'s *"every `_of_natCast_ne_zero` statement below
carries `h2` as well as `hℓ`"* and `…PullbackPrincipalityTwoRationalTorsion`'s *"every statement
below takes `hcard` as **binder**"*, which are three of the fourteen rows below; and its **verb
list is wide**, because the bare stems and *"is an"* catch wordings that
`takes|binds|carries|is stated` does not. **A recogniser published beside a count is an
instrument, and anchoring, case and the verb list are three independent ways for it to be short of
its own rows.** ⚠️ **So run the count
you are about to publish, and assert that every row you name is in its output** — a one-line
membership check, which is what found the fourteenth row below; all fourteen are asserted present
in the 150.

**Fourteen** are a universal over hypotheses or over the setting, sitting outside the `## Main *`
section whose bullets it could be read as clearing. Of those, **one** states a clearance on
itself: `MulByNInertia`, **two** bullets covering **three** declarations, repaired in the row by
this PR. **Four** are the exemption-citation label above. The remaining **nine** clear no bullet:

* three because every bullet of their list names its own hypotheses or names none —
  `EllipticCurves.Torsion.StructureGeneral`, `EllipticCurves.TateModule.FreeGeneral`,
  `…FunctionField.PullbackPrincipalityTwoRationalTorsion`;
* four because the sentence sits **below** its list, which is the *"nothing further up the
  docstring"* half read in the other direction — `…FunctionField.TranslationMulByNCommGeneral`;
  `…PullbackPrincipalityThree` and `…WeilPairingTranslationSlotNotInjective`, each of which
  carries *"Everything below carries `[IsAlgClosed F]`"* in a `## Scope` section printed **after**
  the `## Main *` list it could otherwise be read against; and `…WeilPairingGaloisRootN`, whose
  *"everything general below carries `hprin`"* sits in
  `## ⚠️ What is NOT here, and why it cannot be`, printed after `## Main statements` — and that
  list opens with a register of its own, so no bullet of it was waiting on the later sentence;
* two because what they quantify over is an **instance** or the setting, which `### Reach clauses`
  leaves ambient — `…WeilPairingAlternatingTwoRational` (`[DecidableEq F]`) and
  `…TranslationActionN` (*"at an arbitrary `n` over an arbitrary field"*).

⚠️ **Exclusions with their grounds, because an exclusion needs one as much as a conviction does.**
The bulk of the 150 are non-vacuity paragraphs quantifying over what is **above** them (*"Every
statement above carries `[IsDedekindDomain W.CoordinateRing]`"*), which can clear no bullet below
by construction; and `…PlaceDegreeComparison`'s `## Scope` hit is a marked `### Retired claims`
quotation of a wording that is already gone, not a live claim. The widened alternative adds **22**
lines over the anchored one: **three** are rows already counted above, **one** is the fourteenth,
and the other **18** are excluded on four grounds — **four** sit **inside** their own `## Main *`
section and are safe by construction, **five** quantify over what is **above**, **seven** quantify
over **content, provenance or naming** rather than over hypotheses or the setting, and **two** are
not universals at all but substring matches (*"taken"* on `take`, *"Integrally"* on `all`).

⚠️ **The borderline row is excluded on its *subject*, and that is the whole of the ground.**
`EllipticCurves.TateModule.ImageProfinite`'s *"All fifteen names below carry a `Two`, and all
fifteen statements are byte-identical to what this file shipped before the extraction"* sits in
`## Naming`, printed **above** that file's `## Main statements` — the geometry of a candidate — and
is excluded because it quantifies over **names and byte-identity**, not over hypotheses or the
setting, so it leaves no hypothesis for a bullet to be short of. `…TateModule.FreeGeneral`'s
*"Every statement below is an application"* goes the same way for the same reason. ⚠️ **If that
ground is rejected they are two further rows that *clear*, not two convictions**: neither says a
hypothesis is taken or is absent, so no bullet below them is short of anything they assert.

⚠️ **Every register PR #654 wrote is inside its own `## Main *` section and is safe by
construction**, which is why the convicted count is one and not fourteen: this rule bites on prose
registers written before that PR fixed the placement, and on nothing written from this section.

⚠️ **That `DeterminantModGeneral` opener is the form to copy for the naming half**, and it is
the cheap repair for a list whose bullets are each short of the same hypotheses: name them
**once**, at the head of the list, and say that the bullets do not repeat them. The alternative —
inserting the same two conditions into a dozen bullets — is what `### Scope of the rules above`
calls making the block worse, and it is not what a reader of a list wants.

⚠️ **What it is not the form to copy for is the sentence it closes on**, and a register written
from this document rather than from a sibling file is how that sentence keeps being re-introduced.
*"The bullets give the conclusions and not the hypotheses"* is a universal over the bullets, and it
cannot survive this development's own repairs: a count is repaired **in the row** (*"a register
says what a list omits. It cannot make a count true"*, below), and every such repair costs the
universal another instance. ⚠️ **Nor did it survive its own lists** — the test below is weaker than
a count and most of the blocks that carried it failed it on the day it was written. `#1647` decided
it and PR #658 replaced it in
`EllipticCurves.FunctionField.WeilPairingAlternatingAssemblyN` with the form to copy here — a
**routing** sentence rather than a universal:

> ⚠️ **Where a bullet says nothing about hypotheses, read it against this register; where a
> bullet counts them, the count is that bullet's own claim and no register makes it true.** Naming
> some without counting is neither, and sits under this register unchanged; reporting one
> *discharged* is a gate-discharge claim, which `README.md` `### Gate-discharge claims` governs.

Every branch of it is decided elsewhere in this document and the sentence only routes: silence to
the register, a count past every register, a discharged hypothesis to `### Gate-discharge claims`.
⚠️ **The branch worth reading twice is *"naming some without counting"***, because it is what a
reach-register list is *for* and it is the one a phrase-keyed sweep keeps re-triaging as a defect:
a bullet that names two of its declaration's four hypotheses and claims nothing about the rest sits
under its register **unchanged**, and repairing it in the row is what makes a block worse.

⚠️ **The population, with the recogniser beside it**, because this section's own rule is
*publish the recogniser beside any count, or write no count*. Scan **whole** `## Main *` blocks —
not the prose above the first bullet, since one instance sits inside a bullet and another after the
list — for a sentence carrying both a quantifier (`every`, `all`, `none`, `no `, `each`,
`not read`, `neither`) and a bullet-subject (`bullet`, `row`, `the entries`, `list above/below`),
and **read** every hit rather than counting it. ⚠️ **Date the answer.** At `064208e` with `#1686`
applied — the tree this paragraph ships in — ten `## Main *` blocks in ten files close over their
own bullets, in three live wordings: **one** in `DeterminantModGeneral`'s, which is that block
alone; **eight** in the routing form above (`WeilPairingAlternatingAssemblyN`,
`WeilPairingAlternatingBaseChangeN`, `WeilPairingTranslationSlotHprinN`, `WeilPairingGaloisRootN`,
`WeilPairingAlternatingConsumerN`, `WeilPairingDivisorSlotBilinearHprinN`, `MulByNFibre` — whose
instance is scoped inside a bullet — and `EllipticCurves.Torsion.PrimaryTowerOdd`); and **one**
converse — *"Every bullet above names the whole explicit hypothesis list"*
(`EllipticCurves.Torsion.WronskianSeparable`, over a list that carries no register on purpose, so
*"a register cannot make a count true"* does not bite; its failure mode is the mirror one, going
stale when a bullet is **simplified** rather than completed). A fourth wording — *"the bullets … are
not read for hypotheses at all"* — survives only as `PrimaryTowerOdd`'s own retired quotation
(`#1656`, PR #667), and was live at `ee0b8a4`. That is what the date is for.

⚠️ **Four ways to miscount it, all of them live, and no two agree.** Over the first wording: a
**phrase**-keyed census reads eight where there is one, because the other seven — `…AssemblyN`,
`…AlternatingBaseChangeN`, `…TranslationSlotHprinN`, `…GaloisRootN`, `…AlternatingConsumerN`,
`…DivisorSlotBilinearHprinN` and `MulByNFibre` — each carry it as a retired quotation under
`### Retired claims`, and a retired quotation is not a live universal; and a **line**-keyed `grep`
reads three of those eight, because the phrase wraps mid-sentence in five of them. ⚠️ **The gap
widens with every repair**, since a repair converts a live instance into a retired quotation and
leaves the occurrence count where it was. Over the converse: a **file**-keyed census reads two where
there is one, because `…AlternatingBaseChangeN` quotes `WronskianSeparable`'s sentence as a
cross-reference to another file's register — ⚠️ **and a census that joins lines without collapsing
whitespace cannot see that second occurrence at all**, since the quotation wraps inside an
*indented* bullet and leaves two spaces mid-phrase. Join the lines **and** squeeze runs of
whitespace, or the trap you are publishing a warning about is invisible to your own recogniser.

⚠️ **What falsifies that universal is a bullet that NAMES a hypothesis, not only one that counts
them.** The sentence says the bullets give the conclusions *and not the hypotheses*, so a bullet
that gives one is a counterexample; counting is the narrower, stronger failure that the routing
form's second branch is about. ⚠️ **Do not borrow the routing form's leniency to certify the
sentence it replaced** — *"naming some without counting is neither"* is a branch that form **adds**,
and the want of it is why the old wording had to go. The merged statement of the test is
`WeilPairingAlternatingAssemblyN`'s own retired-claims paragraph, which retires the wording as
*"false already of the first bullet, which has **named** `hprin` and the halving point"*.

⚠️ **`#1647`'s no-sweep instruction stands, and it is an instruction rather than a verdict.**
The rule is to replace the universal *"in the rest as each is touched rather than re-arguing it"*;
this tree does not pre-emptively edit sentences that are not wrong, and nothing here orders a sweep.
But the exemption it grants is *"true of its list"*, and ⚠️ **that truth is a per-bullet reading,
not a property of the phrase**. **Eight** blocks are on record as having carried this wording — the
eight the phrase-keyed census finds — and **seven** have now been read row by row — `…AssemblyN`
(`#1647`), `…AlternatingBaseChangeN` (`#1650`, whose retirement records the read), `…GaloisRootN`
(`#1662`), `…AlternatingConsumerN`, `…DivisorSlotBilinearHprinN` and `MulByNFibre` (`#1686`), and
`DeterminantModGeneral` — and **only `DeterminantModGeneral` held.** (The eighth,
`…TranslationSlotHprinN`, retired the wording on a prose contradiction rather than on a row read, so
it is not counted here.) One falsifying shape is a house idiom rather than an accident: an
`_of_smooth` or `_of_ne_zero` bullet reading *"the same at every `3`-smooth `n ≠ 0`"* or *"at every
`n` with `((n : ℤ) : F) ≠ 0`"* names an explicit binder of its own declaration. ⚠️ **It is not the
only shape** — `MulByNFibre`'s falsifying rows name no index condition at all; they restrict the
ambient quantifier (*"at an affine `P` that is not `n`-torsion"*, *"regular off the `n`-torsion
locus"*) over the very binders that restriction is, which is the same naming in a sentence that does
not look like a reach clause. ⚠️ **So do not write *"the rest are fine"* from a census, and read the
list before quoting a table's `true` column** — a census tells you where a phrase is, never whether
it is true there.

⚠️ **Repairing a sentence already known to be false is not the sweep `#1647` ruled out**, which is
the ground `#1686` repaired the three false blocks on rather than leaving them to the next agent who
happened to touch them. ⚠️ **`DeterminantModGeneral` was left standing on the same ground**: its
universal is true of both its lists, so editing it *would* be the pre-emptive edit `#1647` ruled
out. What the routing form binds unconditionally is the **next** register written or repaired —
including any written from this section.

One file shows the reach half in both directions, and both readings are decided by the signatures
rather than argued:

* **Reached.** `MulByNFibre`'s register is the first bullet of its `### The general layer` sub-list.
  The bullet five rows below it reads *"…`comapProjPointN_add_torsion_of_ne_zero`, and **over
  `F̄`** `…card_fibre_comapProjPointN_projPointOfPoint_of_ne_zero`, …"* — a reach clause naming the
  instance and nothing else, over a signature binding `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` as well.
  Those are the two the register names, so the bullet is compliant relative to it, and repairing the
  row in place would mean repairing all thirteen. ⚠️ **The register is not the whole account of that
  row, and a reach verdict is owed one for every binder.** That signature binds a third hypothesis,
  the transcendence `h`, which the register does not name; it clears on the **derivability**
  exemption, whose price that file has already paid — `MulByNFibre`'s `## The non-constancy
  hypothesis is not named in the headlines below` cites both derivations, and the general one runs
  from `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` — exactly the two the register names.
  ⚠️ **It does not clear as a data argument**, which is what this bullet used to say: `h` is a
  condition on the index, and `### Reach clauses` convicts exactly that omission by name in
  `ramificationIdxN_pos`. Same verdict, and not the same ground (`#1631`).
* **Not reached.** The **outer** `## Main statements` list higher up the same docstring is a
  different block. Its own head is *"⚠️ Every public declaration of this file is listed"* and
  declares no register, so its bullets are read against that and get nothing from the sub-list below
  them — including the two that carry a reach clause of their own over signatures binding more
  (`#1616`).

And the gate-discharge half, where the subject legitimately sits two `##` sections above the list:
`residueDegreeN_none_eq_one` (`EllipticCurves.FunctionField.MulByNResidueDegree`) is bulleted
*"`f_∞ = 1`, at every `n` at which `[n]` is non-constant, unconditionally"* under a list whose head
declares no register at all. The word's subject is written out in full under that module's
`## ⚠️ The residue degree at infinity is *not* in the composition class` — the declaration *"holds
at every `n` at which `[n]` is non-constant, with no `3`-smoothness, no `(2 : F) ≠ 0`, no
`(3 : F) ≠ 0`, no `[IsAlgClosed F]`"* — and that is a gate list, the hypotheses `#1214`'s
composition route carries and this one does not. A subject, not a hypothesis list, and compliant
where it stands.

⚠️ **Read the two clauses of that bullet separately, because the halves decide independently — and
this row is the worked example of their deciding differently.** The gate-discharge half was
compliant throughout. The reach half was **not**, and it is the half that had to be repaired.

**The old reading, retired** (`### Retired claims` below): until `#1636` (PR #653) the row read
*"`f_∞ = 1`, at every `n`, unconditionally"*, naming no index condition at all. This document
used to clear that on the ground that the declaration's one propositional binder is a **data
argument of the object the bullet is about** — `residueDegreeN n hn p` does not typecheck without
it, so there was *"no reach for the clause to misreport"*. `### Reach clauses` withdraws that ground
(`#1631`): `hn` is a condition on the index, which is one of the two things a reach clause reports,
and that section convicts the identical omission by name in `ramificationIdxN_pos`, whose signature
is this one. ⚠️ And *"unconditionally"* is the strongest form of a clause, not a mitigation of it —
which is why the repair **kept the word, in place**, and moved only the reach half. A bullet that
mixes the registers is answerable to both, and a row that clears is not evidence that it cleared on
the ground you had in mind.

⚠️ **That list's head still declares no register, and the reason is worth a clause of its own.** The
`DeterminantModGeneral` opener above is *"the cheap repair for a list whose bullets are each short
of the same hypotheses"*, and `…residueDegreeN_two` and `…residueDegreeN_three` bind **no**
transcendence — they take `(2 : F) ≠ 0`, the second `(3 : F) ≠ 0` as well, and derive it. A register
saying every statement below takes the non-constancy would be **false** of them: the opener's
*"each"* is doing the work, and a row that **derives** a hypothesis fails that test exactly as a row
that never needed it would. So the repair named the condition in the rows that make a claim
about which `n` are reached — this one and `…residueDegreeN_eq_one` — and the module block
records why there is no register, so the next census does not re-measure the list to find out.

⚠️ **A register says what a list omits. It cannot make a count true.** So a register's reach stops
exactly where `### Gate-discharge claims` stops, and for the same reason: *"the whole hypothesis
list"*, *"the single hypothesis"*, *"from nothing but"*, *"and nothing else"* are claims about the
hypothesis list itself, and no sentence elsewhere in the block supplies a member such a claim
excludes. The compliant form is `ψ_pair_mul_of_ψ_eq_zero`
(`EllipticCurves.Torsion.OmegaPairCoprime`), bulleted *"at every `n : ℤ` and with no hypothesis but
`ψₙ(x, y) = 0`"* over a signature whose one propositional binder is that equation.

⚠️ **The traffic runs one way.** A block repairs a bullet; a bullet repairs nothing. Under
`### Scope of the rules above` a module list and the file's headlines are two blocks, so a row this
section clears as a bullet is still held to the rules above as a headline, and the two layers are
repaired separately. **A sibling bullet is not a register either** — it is a bullet, so a count in
one bullet is not completed by the hypotheses another bullet of the same list happens to name.

⚠️ **This is not a further exemption, and it must not be counted as one.** `### Reach clauses` above
states its exemptions and `### Gate-discharge claims` adds the next; this section adds none. It is a
**scoping** rule — it says which text a bullet is read against — and every exemption above then
applies to a bullet exactly as it does to a headline.

⚠️ **And it does not reopen *"a phrase a file coins for itself earns nothing here"*** in
`### Gate-discharge claims`. That clause governs a **declaration headline**, whose unit is its own
docstring, and it turns on an asymmetry it names: a reader who meets a partial hypothesis list in a
headline *"has no signal that a completing sentence exists anywhere"*. A bullet's own docstring
**is** the module docstring. A register at the head of its list is *in the same docstring* rather
than *"prose sitting elsewhere in the module"*, and the reader of a bullet is reading the list. The
boundary is unchanged; the **unit** moves with the layer, which is the same fact stated twice.

Measured at `7495d3e`, and the two halves of this paragraph are of different qualities. **1696**
bullets in **425** `## Main *` sections — reproduced to the unit by three independently written
extractors — spread over **364** of the tree's **419** module docstrings. Measured **once**, on
`#1614`, by a join against the elaborated environment: **1690** of the 1696 resolve to a declaration
of this development, the misses being anonymous `instance :` rows, brace-contracted name patterns
and two prose bullets. **59** rows are triaged individually on `#1614` and are named there.

⚠️ **That 59 is a triage set, not a measurement, and the number should not be quoted as one.** It
was found with a phrase list — `the whole hypothesis list`, `the only hypothesis`,
`the single hypothesis`, `the only gate`, `unconditional`, `with no hypothesis`,
`no hypothesis beyond`, `the entire hypothesis`, `the only input` — and on this tree that list is
not stable under choices no one would think to publish. The same nine phrases over the same 1696
bullets return **57** matched case-sensitively, **59** case-insensitively, and **54** if a bullet is
terminated at the end of its list instead of absorbing the module prose that follows it; four
further phrases the tree does use (`nothing else`, `nothing but`, `no other hypothes…`,
`the only remaining`) add **6** more. `#1584` is the standing record of what a phrase list does to
this front, and this is the same fact one layer up: **publish the recogniser beside any count, or
write no count.** The remaining ~1640 bullets have not been read on this axis, and this section is
not a claim about them.

### Scope of the rules above

They apply **per block, not per phrase** — a `## Main statements` list, or a `generality` table
column, is one place. A fix that repairs one row and leaves its neighbour partial makes the
block worse rather than better, because the reader now has two rows in different registers and
no way to tell which is which.

Consequences worth stating, because each has cost a review cycle. ⚠️ **Their number is
deliberately not given** (`#1667`): this line read *"Four consequences worth stating"* from
`f1d1473` (`#1569`, PR #620) onwards and was true until the *"A heading is one source line"*
bullet below made it five, in the same PR that wrote the bullet. A numeral standing over a list
is falsified by whatever next extends the list, and no bullet under it can repair the numeral —
which is `### Module-block bullets`' *"A register says what a list omits. It cannot make a count
true"*, one layer up, in this document's own prose. They are:

* **The subject decides, not the string.** *"it is `natDegree_ΨSq` that needs `(n : F) ≠ 0`"*
  is correct — Mathlib's `natDegree_ΨSq` asks that and nothing else — while the identical
  phrase about a statement of this development that also takes `h2` is a defect. Resolve each
  clause's subject to a declaration and read its binders; a `grep`-keyed sweep of this class
  produces false positives as well as false negatives.
  ⚠️ **A reach clause is a clause, not a sentence** (`#1679`). A sentence can carry two subjects,
  and a condition named for one of them does **not** reach the other; a census keyed on sentences
  cannot see the difference, because the sentence passes its field test on either subject's
  strength. The instruction above therefore reads *"each clause's subject"*; it read *"the
  sentence's subject"* until `#1679`, which is a **completion** and not a retirement — the old
  words were partial rather than false, which is the test `### Reach clauses` sets.
  ⚠️ **The class is anti-monotone under this front's own repair programme**, so it does not shrink
  on its own: repairing one clause is what hides its neighbour. All four rows `#1679` found are
  `#1137`'s own residue — PR #602, PR #605 and PR #616 each wrote `(2 : F) ≠ 0` into the clause
  beside `nsmul_surjective_of_two_ne_zero`'s and left that one naming the index alone, and from
  each of those commits a sentence-keyed test reads the whole sentence as clear.
  ⚠️ **A list item is a unit too.** Two of the four are bullets, where what the reader meets is
  the bullet and not the sentence a splitter would cut out of it.
* **`(n : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` are different clauses.** The `_of_natCast_ne_zero`
  and `_of_intCast_ne_zero` suffixes say which, and a reach clause should match the suffix.
* **Declaration headlines are reach clauses too**, and doc-gen surfaces them in preference to
  module prose. A `## Hypotheses` section elsewhere in the same module does not repair a
  partial headline. ⚠️ **Nor does a sentence lower in the declaration's own docstring** (`#1660`).
  This is where this rule and `### Gate-discharge claims` part company, and not a second
  application of one boundary: that section's exemption is *"in the same docstring"* precisely
  because a gate-discharge word is **visibly relative to something**, so a reader who meets one
  knows a subject for it exists and reads on. `### Module-block bullets` states the asymmetry —
  *"A partial reach clause carries no signal at all, so the register has to be where the reader
  meets it"* — and for a headline the place the reader meets the clause **is** the headline.
  The worked case is `residueDegreeN_none_eq_one`
  (`EllipticCurves.FunctionField.MulByNResidueDegree`), whose headline read *"`[n]∗` is residually
  trivial at the point at infinity, at every `n`"* four lines above a ⚠️ naming the non-constancy
  as *"the only thing `n` is asked for"*: the ⚠️ was true, the headline was false at `n = 0`, and a
  reader who stopped at the headline had nothing telling them not to.
  ⚠️ **The paragraph opening this section decides it the same way**, which is what makes the
  ruling cheap rather than a new cost: that headline's two neighbours in the same section were
  short of the same condition and take the insertion on nobody's argument, so clearing this one
  would have left the block with rows in two registers and no way to tell which is which.
* **A heading is one source line, because a heading that wraps is a heading that is cut off
  there** (`#1667`). A Markdown ATX heading (`# `, `## `, …) is a leaf block that ends at the end
  of its line, and there is no continuation syntax, so a title written across two lines renders as
  a heading containing the first line and an ordinary **paragraph** containing the rest. The reader
  who consults the heading — the reader this section's previous bullet is about — is therefore
  given a clause chopped at whatever word the line broke on:
  `EllipticCurves.FunctionField.MulByNFibre`'s H1 named two index ranges and doc-gen printed
  *"…and the fibre over one — at"*. ⚠️ **The hundred-column limit is therefore a limit on what a
  heading may *say*, not only on how it is typed**: a title that does not fit has to be shortened,
  and a reach clause that does not fit inside the shortened title has to be dropped to the
  *"or it names none"* branch of `### Reach clauses` and stated in the prose below, not wrapped.
  ⚠️ **Prefixing the second line with its own `#` does not join it either** — it makes a *second*
  heading. `EllipticCurves.FunctionField.WeilPairingDivisorSlotBilinearHprinN` carried
  *"…and it stopped being so"* / *"twelve hours ago"* as two `##`s, and doc-gen printed
  *"twelve hours ago"* as a section of the module. ⚠️ That variant is invisible to a census keyed
  on *"a heading followed by prose"*, which is how it survived the sweep that found the other
  three: read every heading whose text begins in lower case as well.
  ⚠️ It is only headings. A paragraph, a bullet and a `**bold**` span all cross a line break
  correctly, and several repairs on this front rely on that.
* **Sort the class before repairing it, and expect to do two things at once.** A headline that
  lists too few hypotheses takes an **insertion**; one that *also* asserts there are no others takes
  that insertion **and** a deletion or a re-scoping of the assertion — because *"with `(2 : F) ≠ 0`
  … as the only hypothesis"* names a hypothesis and then denies there is one. Both forms are on the
  board, and neither is insertion-free:
  * **Delete the assertion.** `card_torsion_pow_of_separable` and `finite_torsion_pow_of_separable`
    (`EllipticCurves.Torsion.OddTorsionCount`, PR #619) read *"at an odd `p`, from separability of
    `preΨ p` **alone**"*. The repair dropped *"alone"* **and** added the two conditions the list was
    short of, giving *"with `(2 : F) ≠ 0`, at an odd `p` with `(p : F) ≠ 0`, from separability of
    `preΨ p`"*. ⚠️ Deleting *"alone"* and stopping there would have left `h2` and `(p : F) ≠ 0`
    unnamed under a headline that still named `Odd p` — a proper non-empty subset, the defect again.
  * **Re-scope it**, which is the form to prefer wherever the word is true of a gate. Three of the
    `card_torsion_eq_sq_*` headlines (PR #622) said *"and nothing else"*;
    `card_torsion_eq_sq_of_wronskian_identity` went from *"at odd `n`, from the Wronskian identity
    **and nothing else**"* to *"with `(2 : F) ≠ 0`, at odd `n` with `(n : F) ≠ 0`, with the
    Wronskian identity **the only gate left**"*: the noun moves from *hypothesis* to *gate*, and the
    insertion then goes in beside it without contradiction. See `### Gate-discharge claims` above,
    which is what the re-scoped word is then read under.
    ⚠️ **The body prose has to follow the headline.** The same PR changed *"it is now the only
    **hypothesis**"* to *"the only **gate**"* and *"no second **hypothesis**"* to *"no second
    **gate**"*, a few lines below two of those headlines. A repair that stops at the headline leaves
    the docstring contradicting itself.

### Retired claims

A clause that a later PR falsifies is kept as a **marked quotation** — the old text in
italics, attributed, followed by what replaced it — rather than deleted, so that a reader who
remembers the old claim learns why it went. ⚠️ **Retired declaration names are written in
italics, not backticks.** Backticks are how this development marks a live citation, and every
name-resolution check keys on them; a retired name in backticks is indistinguishable from a
dangling one.

⚠️ **A clause replicated into many blocks retires once if those blocks share its subject, and once
per block otherwise.** `#1694` is what forced the question: one sentence about
`WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero` was copy-pasted into 37 module blocks by a
single sweep (`5d6884a`, PR #561), and read literally this section asked for 37 quotations of it. It
asks for **one**, in `EllipticCurves.Torsion.OmegaCrux` — the file that defines the declaration the
clause was about — because the 37 copies asserted **one proposition, not 37**: each said the same
thing about the same declaration, one reading of one signature falsified all of them at once, and
the reader this section serves is a reader who wants to know what that declaration says. ⚠️
**Contrast the two wordings that were retired once per block, at each site that falsified them**,
neither of them replicated any less: *"the bullets give the conclusions and not the hypotheses"*
across seven blocks (`#1647`, `#1650`, `#1662`, `#1686`) and *"no reach clause names it"* across
five (`#1688`, `#1696`). Both are universals over **the block's own list**, so each copy is a
different proposition falsified by a different list, and one quotation elsewhere would leave every
other block with no account of why its own sentence changed. ⚠️ **Both wordings are also still LIVE
at one site each, and that is this test working rather than an exception to it**:
`EllipticCurves.TateModule.DeterminantModGeneral` carries the first (eight blocks held it, seven
retired) and `EllipticCurves.FunctionField.MulByNSeparable` the second (six held it, five retired),
each read row by row and each true of *that* block's own list. **Occupancy never triggers this
section; falsification does**, so the counts above count retirements and not copies. **The test is
what the clause is about — not how many files carry it, and not how many PRs repaired it.** A claim
about the block it sits in retires where it sits; a claim about a subject that lives elsewhere
retires at the subject, once. ⚠️ Apply `### Reach clauses`' *"Read whether the old clause was false
or merely partial"* first: it decides whether this section binds at all, and only then does the
count above apply. ⚠️ **No census width changes either way.** `### Module-block bullets` already
prices the phantom that a retirement leaves in a phrase-keyed count, and says the gap widens with
every repair; that cost is accepted there and is **not** what decides placement here. ⚠️ **The rule
is retrospective and nothing is owed to it** — both rulings on record already comply, which is why
this paragraph states the tree rather than changing it.

## Building

This project pins a specific Mathlib revision via `lake-manifest.json` and the
matching toolchain in `lean-toolchain`. To build:

```bash
lake exe cache get   # download the Mathlib build cache
lake build
```

## Linting

Two different linter suites apply to this project, and they are easy to confuse.

* The **syntactic** linters run during elaboration and surface as build warnings.
  They are enabled by `weak.linter.mathlibStandardSet = true` in `lakefile.toml`,
  and `lake build --wfail` (see below) is what enforces them.
* The **environment** linters — `simpNF`, `unusedArguments`, `defsWithUnderscore`,
  `docBlame`, `synTaut`, `checkType`, `deprecatedNoSince`, `impossibleInstance`,
  `nonClassInstance`, `simpComm`, `structureInType`, `subsetDotNotationLinter`,
  `tacticDocs`, `unusedHavesSuffices` — are a **post-hoc pass over the elaborated
  environment**, run by Batteries' `runLinter` driver. `lake build` never invokes
  them, so a green, warning-free build says nothing at all about them.

Run the second suite with:

```bash
lake lint            # auto-detects the default target, `EllipticCurves`
```

It takes roughly 10–20 s on top of a warm build (measured: ~11 s locally, 15–18 s on a
CI runner), and prints `-- Linting passed for EllipticCurves.` when clean.

CI runs it on every push and pull request: `leanprover/lean-action@v1` probes with
`lake check-lint` and runs `lake lint` itself when it finds a driver. **The driver is the
single line `lintDriver = "batteries/runLinter"` in `lakefile.toml`**, and it is
load-bearing. Remove it and the two halves behave very differently:

* `lake lint` **fails loudly** — `error: no lint driver configured and builtin linting
  is disabled`, exit 1. Locally you cannot miss it.
* CI, under `lean-action`'s default `lint: default`, would **not**: the probe fails, the
  action logs `lake check-lint failed -> will not run lake lint`, and the job stays green
  with the suite never run. That is the silent failure mode, and it is why the workflow
  passes `lint: "true"` explicitly — that setting turns a missing driver into
  `::error::lake check-lint failed: could not find a lint driver` and a red job, rather
  than a skipped step.

That silence is not hypothetical: the suite had never been run on this repository at
all, and when it first was, it reported 53 findings — 33 `@[simp]` lemmas whose
left-hand side was not in simp-normal form (so they could never fire), 16 naming
violations and 4 unused hypotheses — against a build that was, and had always been,
warning-free.

## Development

The `.orchestra/` folder contains scripts used to prepare and validate the
project in an automated setting:

* `before.sh` warms the Mathlib build cache.
* `validation.sh` checks that the worktree is clean, that every `.lean` file is
  imported (`mk_all --check`), that the project builds with warnings treated as
  errors (`lake build --wfail`), and that the environment linters pass
  (`lake lint`; see [Linting](#linting) — the last two are different suites).
