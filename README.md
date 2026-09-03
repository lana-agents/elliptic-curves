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

* **A phrase that quantifies the conclusion's own bound variable is not a reach clause**; a phrase
  that enumerates the conditions under which the statement holds is. *"Away from the multiples of
  the least vanishing index, `ψ` does not vanish"* (`ψ_evalEval_ne_zero_of_not_dvd`) is the
  `∀ m, ¬(d ∣ m)` **inside** the conclusion, not a restriction on when the theorem applies. Same
  for `ψ_evalEval_eq_zero_of_dvd`, `divT_add_mul_of_not_dvd` and `divY_add_mul_of_not_dvd`.
* **A phrase about a fixed numeral is a remark, not a reach clause.** *"`#E[10] = 100`, at an index
  that is neither odd nor `3`-smooth"* (`card_torsion_ten`) cannot be a hypothesis list, because
  `10` is not quantified and there is nothing for a condition to range over. Same for
  `nonempty_torsionThirtySix_addEquiv`, `card_torsion_four`, `nonempty_torsionFour_addEquiv` and
  `nonempty_torsionTwelve_addEquiv`.

⚠️ The second discriminator is what separates *"at an index that is neither odd nor `3`-smooth"*
from *"at an odd `p`"*: the first describes the numeral `10`, while the second restricts a variable
and so is a reach clause bound by the rule.

The rule is about **explicit** hypotheses. Instance arguments are ambient, are carried by the
module's `variable` block, and are visible in the signature doc-gen renders beside the docstring
— so a reach clause need not list them. But a clause that *does* make an instance claim
(*"with no `[IsAlgClosed F]`"*) is making a complete-list claim about instances, and then the
same rule applies to those: name all of them or none.

The rule binds every **explicit** hypothesis, with one narrow exemption: a clause may omit a
hypothesis that is **derivable from the hypotheses the clause does name**, since such a hypothesis
adds no reach information the clause has not already given. Where the exemption is used, the
derivation is cited once in the module block, so a reader can check it instead of taking it.

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

⚠️ **The exemption is about derivability, not about where the hypothesis appears.** A rule keyed
on *"the hypothesis occurs in the conclusion"* would reach `(2 : F) ≠ 0`, which is an explicit
argument of `mulByTwoEndo`, `mulByThreeEndo`, `comapProjPointTwo` and `weilPairingTwo`, and so
occurs inside the conclusion of every statement about them. `(2 : F) ≠ 0` is derivable from nothing
any reach clause on this development names — not from `3`-smoothness, not from `(n : F) ≠ 0` — so it
is reach, and the rule binds it. Omitting it is the defect class `#1137` exists to pay off.

It applies **per block, not per phrase** — a `## Main statements` list, or a `generality` table
column, is one place. A fix that repairs one row and leaves its neighbour partial makes the
block worse rather than better, because the reader now has two rows in different registers and
no way to tell which is which.

**A gate-discharge claim is relative to the gate list it names**, and the rule binds it only where
that list is not named. *"With no hypothesis left"*, *"with `#E[p] = p²` as the only hypothesis"*
and *"from the count at `p` alone"* do not enumerate the conditions under which a statement holds;
they say which entry of a gate list published elsewhere a statement has discharged. There is no
enumeration for the binders to be a proper subset of, so the rule above has nothing to bind —
**provided the gate list is named where the claim is made**.

`nonempty_torsionPow_addEquiv_of_odd` (`EllipticCurves.Torsion.PrimaryTowerOdd`) is the worked
case. Its headline reads *"The structure theorem for `E[pᵏ]` at an odd prime `p`, with no
hypothesis left"* while the theorem binds four hypotheses, and the next sentence of the same
docstring names the list and spells it out — *"the signature `EllipticCurves.Torsion.PrimaryTower`'s
gate list reduces to … over an algebraically closed field with `(2 : F) ≠ 0`, at an odd prime `p`
with `(p : F) ≠ 0`"*. Compliant — and not an exception to the *"declaration headlines are reach
clauses too"* consequence below. That one is about a `## Hypotheses` section **elsewhere in the
module**, which doc-gen does not render beside the headline; this sentence is in the same docstring.

⚠️ **A gate-relative register is a per-file object, and an instrument that reads one declaration at
a time cannot see it.** `EllipticCurves.Torsion.PrimaryTowerAlgClosed` factors its field conditions
into a `## What the substitution costs` section and then writes its headlines relative to what is
left, its H1 included (*"`#E[p] = p²` is the only hypothesis left"*). Repairing one row of such a
file and leaving the rest is the per-block harm above, one level up: where a module factors its
hypotheses out on purpose, the headline **is** the register, and changing it is a decision about the
whole file rather than a sweep item.

⚠️ **This is not an exemption for every headline that mentions a gate.**
`card_torsion_pow_of_odd` (same file as the worked case) said *"at an odd `p`, unconditionally"* and
was a defect: *"at an odd `p`"* names `hodd` and omits `hp : (p : F) ≠ 0`, and both are conditions
the statement puts on its **index**, not entries of a gate list. A clause naming one of two index
conditions is a proper non-empty subset however the gate word is read.

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
* **Sort the class before repairing it.** A headline that lists too few hypotheses takes an
  **insertion**; a headline that asserts there are no others takes a **deletion or a re-scoping**.
  Adding `(2 : F) ≠ 0` beside *"as the only hypothesis"* yields a sentence that contradicts itself.
  `card_torsion_pow_of_separable` and `finite_torsion_pow_of_separable` lost the word *"alone"*;
  `card_torsion_pow_of_odd` had *"unconditionally"* re-scoped to *"and with no `hcard`"*, which is
  what the word was actually true of — so that claim came out sharper than it went in.

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
