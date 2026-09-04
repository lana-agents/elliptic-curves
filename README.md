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

**Two phrases look like reach clauses and are not.** Both have been flagged, triaged and cleared
more than once, so the discriminators are written down here rather than re-derived each round:

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
* **A phrase about a fixed numeral is a remark, not a reach clause.** *"`#E[10] = 100`, at an index
  that is neither odd nor `3`-smooth"* (`card_torsion_ten`) cannot be a hypothesis list, because
  `10` is not quantified and there is nothing for a condition to range over. Same for
  `nonempty_torsionThirtySix_addEquiv`, `card_torsion_four`, `nonempty_torsionFour_addEquiv` and
  `nonempty_torsionTwelve_addEquiv`.

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

⚠️ **This paragraph is not a third discriminator for the bullet list above.** It does not say that
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
  `EllipticCurves.FunctionField.MulByNFibre` (*"**Every one of the thirteen below does take both**,
  and the bullets give the conclusions and not the hypotheses"*) and
  `EllipticCurves.TateModule.DeterminantModGeneral`, whose `## Main statements` **opens** *"**Every
  statement and definition below takes `(2 : F) ≠ 0` and `(n : F) ≠ 0`**, and the rank and the basis
  take `1 < n` as well; the bullets give the conclusions and not the hypotheses"*.
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

⚠️ **That `DeterminantModGeneral` opener is the form to copy**, and it is the cheap repair for a
list whose bullets are each short of the same hypotheses: name them **once**, at the head of the
list, and say that the bullets do not repeat them. The alternative — inserting the same two
conditions into a dozen bullets — is what `### Scope of the rules above` calls making the block
worse, and it is not what a reader of a list wants.

One file shows the reach half in both directions, and both readings are decided by the signatures
rather than argued:

* **Reached.** `MulByNFibre`'s register is the first bullet of its `### The general layer` sub-list.
  The bullet three rows below it reads *"…`comapProjPointN_add_torsion_of_ne_zero`, and **over
  `F̄`** `…card_fibre_comapProjPointN_projPointOfPoint_of_ne_zero`, …"* — a reach clause naming the
  instance and nothing else, over a signature binding `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` as well.
  Those are the two the register names, so the bullet is compliant relative to it, and repairing the
  row in place would mean repairing all thirteen.
* **Not reached.** The **outer** `## Main statements` list higher up the same docstring is a
  different block. Its own head is *"⚠️ Every public declaration of this file is listed"* and
  declares no register, so its bullets are read against that and get nothing from the sub-list below
  them — including the two that carry a reach clause of their own over signatures binding more
  (`#1616`).

And the gate-discharge half, where the subject legitimately sits two `##` sections above the list:
`residueDegreeN_none_eq_one` (`EllipticCurves.FunctionField.MulByNResidueDegree`) is bulleted
*"`f_∞ = 1`, at every `n`, unconditionally"* under a list whose head declares no register at all.
The word's subject is written out in full under that module's
`## ⚠️ The residue degree at infinity is *not* in the composition class` — the declaration *"holds
at every `n` at which `[n]` is non-constant, with no `3`-smoothness, no `(2 : F) ≠ 0`, no
`(3 : F) ≠ 0`, no `[IsAlgClosed F]`"* — and that is a gate list, the hypotheses `#1214`'s
composition route carries and this one does not. A subject, not a hypothesis list, and compliant
where it stands.

⚠️ **Read the two clauses of that bullet separately, because the halves decide independently.**
*"At every `n`"* is a reach clause and gets nothing from two sections up; it is compliant for the
other reason, that the declaration's one propositional binder is a **data argument of the object
the bullet is about** — `residueDegreeN n hn p` does not typecheck without it, so there is no reach
for the clause to misreport. A bullet that mixes the registers is answerable to both, and a row
that clears is not evidence that it cleared on the ground you had in mind.

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

Four consequences worth stating, because each has cost a review cycle:

* **The subject decides, not the string.** *"it is `natDegree_ΨSq` that needs `(n : F) ≠ 0`"*
  is correct — Mathlib's `natDegree_ΨSq` asks that and nothing else — while the identical
  phrase about a statement of this development that also takes `h2` is a defect. Resolve the
  sentence's subject to a declaration and read its binders; a `grep`-keyed sweep of this class
  produces false positives as well as false negatives.
* **`(n : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` are different clauses.** The `_of_natCast_ne_zero`
  and `_of_intCast_ne_zero` suffixes say which, and a reach clause should match the suffix.
* **Declaration headlines are reach clauses too**, and doc-gen surfaces them in preference to
  module prose. A `## Hypotheses` section elsewhere in the same module does not repair a
  partial headline.
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
