/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.CoordinateRingUnits
import EllipticCurves.FunctionField.MulByTwoEndomorphism
import EllipticCurves.FunctionField.MulByThreeEndomorphism

/-!
# The Weil-pairing element `e_n(S, T)` (Weil-pairing construction, rung 6)

Let `W` be a Weierstrass curve over a field `F` whose affine coordinate ring `F[W]` is a Dedekind
domain.  The divisor-theoretic Weil pairing (Silverman AEC III.8) is built from the `n`-th root
`g_S ∈ F(W)` of the pulled-back principal function of a nonzero `n`-torsion point `S` (rung 5,
issue #418): a nonzero `g_S` with

```
u · g_S ^ n = [n]∗ f_S   (u a unit of F[W], [n]∗ = mulByTwoEndo the multiplication-by-n pullback).
```

For a second `n`-torsion point `T = (x₂, y₂)` with translation endomorphism
`τ_T∗ = translateEndo h₂ : F(W) →+* F(W)` (issue #406), the pairing value is the ratio

```
e_n(S, T) := τ_T∗(g_S) / g_S ∈ F(W).
```

This file defines that element (`weilPairingElt`) and proves its defining property — that it is an
`n`-th root of unity, `e_n(S, T) ^ n = 1` — reduced to the single algebraic fact that the
translation fixes `g_S ^ n`:

* `weilPairingElt`               — the element `τ_T∗(g_S) / g_S`;
* `weilPairingElt_ne_zero`       — it is nonzero (for `g_S ≠ 0`);
* `weilPairingElt_pow_eq_one`    — `e_n(S, T) ^ n = 1` from `translateEndo h₂ (g_S ^ n) = g_S ^ n`.

## Why `τ_T∗` fixes `g_S ^ n`, and the scope delivered here

The reason `τ_T∗` fixes `g_S ^ n` is the geometric identity `[n](P + T) = [n]P` (valid because
`T` is an `n`-torsion point, `[n]T = O`): pulling `[n]∗ f_S = u · g_S ^ n` back by `τ_T` leaves it
unchanged, so `τ_T∗(u · g_S ^ n) = u · g_S ^ n`.  Cancelling the unit `u` (which `τ_T∗` also fixes,
being a nonzero constant of `F[W]`) yields `τ_T∗(g_S ^ n) = g_S ^ n`.

This file therefore packages the **Ward- and normality-independent algebra** of rung 6: the
definition of `e_n(S, T)`, its non-vanishing, and the `μ_n`-membership `e_n ^ n = 1`, reduced via
`translateEndo_pow_eq_self_of` to exactly two named inputs on the concrete `n = 2`/`n = 3` data —

* `hcomm : translateEndo h₂ ([n]∗ f_S) = [n]∗ f_S` (the `[n](P + T) = [n]P` commuting identity),
* `huf`   : `translateEndo h₂` fixes the unit `u`  (the unit `u` of `F[W]` is a constant),

both of which are genuine rational-function identities carried here as hypotheses, to be discharged
by a follow-on.  Everything else — the definition, non-vanishing, the `n`-th-root-of-unity property,
and the cancellation reducing the two inputs to `τ_T∗(g_S ^ n) = g_S ^ n` — is unconditional.

## Explicitly out of scope (as issue #419 records)

* **Bilinearity, alternating, Galois-equivariance** — separately valuable follow-ons, and all three
  have since landed elsewhere on this front, over `F̄` (`WeilPairingDivisorSlotBilinear`,
  `WeilPairingTranslationSlotBilinear`/`…Hom`, the `WeilPairingAlternating*` family,
  `WeilPairingGaloisRoot`) **and** over an arbitrary base field with the principality hypothesis
  `hprin` the single shared gate, at `n = 2` and `n = 3` and at both the `F(W)` and `μ_n(F)`
  levels — six families in all, `#899` (by base change, `WeilPairingAlternatingBaseChange`) and
  `#907`/`#910`/`#912`/`#913`/`#923` (each the `…Hprin` twin of a merged `F̄` file).
  ⚠️ **Do not compress that into "rung 6 is complete over an arbitrary field".**  A completeness
  claim needs its domain stated, and the domain is those six families and no more.
  **Non-degeneracy is not among them and is not a lift**: `WeilPairingNondegenerateTwo` carries a
  second, independent `[IsAlgClosed F]` dependence through `card_torsion_two` (`#759`), and
  non-degeneracy against `E(F)[n]` over a non-closed `F` is *false*, so there is nothing there to
  lift and filing it as one would be an error.  ⚠️ The undomained version of that sentence is what
  `#923` was filed to correct, three times over: **enumerate the domain from the issue tree, not
  from the files you happen to have open.**
* **Packaging `e_n` as a function of two points** — done at `n = 2`, not here:
  `EllipticCurves.FunctionField.WeilPairingFunctionTwo` (`#922`) defines
  `weilPairingTwo : E[2] → E[2] → μ_2(F)`, bundles it as `weilPairingTwoHom` and states
  non-degeneracy as `ker_weilPairingTwoHom h2 = ⊥`.  ⚠️ It is stated over `[IsAlgClosed F]` and has
  **no** `_of_hprin` twin, deliberately: its single gate produces a *witness*, and `#899`'s test
  says base change never reaches those.  ⚠️ **This is the first file on this front where the
  single-gate rule and `#899`'s test disagree**, and the two are not the same test.  The `n = 3`
  mirror is `EllipticCurves.FunctionField.WeilPairingFunctionThree` (`#925`), which defines
  `weilPairingThree : E[3] → E[3] → μ_3(F)`, bundles it as `weilPairingThreeHom` and states
  `ker_weilPairingThreeHom h2 h3 = ⊥`; it carries the same single gate and, for the same reason,
  the same absence of an `_of_hprin` twin.
* **Non-degeneracy** — out of scope *of this file*, and **not** Ward-gated; see the next section,
  which is the canonical account of what it consumes.  Over an algebraically closed base field it
  is merged at both `n`, as `EllipticCurves.FunctionField.WeilPairingNondegenerateTwo` (`#796`) and
  `EllipticCurves.FunctionField.WeilPairingNondegenerateThree` (`#831`); over a general field at
  either `n`, it is not.
* **General `n`** — needs the general `[n]∗` (#404 crux); only `n = 2, 3` are concretely available.
* The normality discharge `IsIntegrallyClosed W.CoordinateRing` — out of scope of this file because
  it is **done**, not because it is blocked.
  `EllipticCurves.FunctionField.CoordinateRingNormalGeneral` registers it, and Dedekindness with
  it, as a global **instance** for `[W.IsElliptic]` over an **arbitrary** field.  That is why the
  single `variable` line below carries no Dedekind hypothesis, and why nothing downstream has to
  supply one.  ⚠️ Said relative to the file rather than by line number, which rots: the number
  first written into this bullet was already stale when it was pushed, and the bullet's own added
  lines then moved the block again.

## What non-degeneracy actually consumes (`#769`) — the canonical statement

⚠️ Until `#769` this file and seventeen others said non-degeneracy was *"Ward-gated (`#242`)"* or
*"needs `#E[n] = n²` (`#242`)"*.  **Both halves of that are wrong**, and they are wrong differently
at the two `n` this tree can state the pairing at.  The other sites now point here rather than
restate the gate; keep it that way, so that the next fact to land has one sentence to refresh and
not eighteen.

Silverman *AEC* III.8, Prop. 8.1(d): if `e_n(S, T) = 1` for every `T ∈ E[n]` then `S = O`.  Read at
`n = 2`, for `S = (x, y)` a nonzero affine `2`-torsion point, the argument is

1. take `g_S ≠ 0` with `u · g_S ^ 2 = [2]∗ f_S` — `exists_gS_two` (`NthRootOfPullback`), whose
   hypothesis `hprin` was the **one gated input** and is discharged over `[IsAlgClosed F]` by
   `#791` (see below);
2. `e_2(S, T) = 1` says exactly `τ_T∗ g_S = g_S` — merged, as
   `weilPairingElt_eq_one_iff_translateEndo_fixed` (`WeilPairingAlternating`, `#465`);
3. so `g_S ∈ Fixed(E[2])`, via `mem_fixedFieldTwo_iff` and `translateAut_apply_some`
   (`TranslationAction`), which is `rfl` onto `translateEndo` — a case split on `W.Point`, no new
   mathematics;
4. `Fixed(E[2]) = [2]∗F(W)` — `fixedFieldTwo_eq_mulByTwoFieldRange` (`MulByTwoGalois`, `#759`),
   **merged**, under `[IsAlgClosed F]` and `(2 : F) ≠ 0`;
5. writing `g_S = [2]∗ h` and cancelling: the unit `u` is a constant
   (`exists_eq_algebraMap_of_isUnit`), `[2]∗` fixes constants (`mulByTwoEndo_algebraMap_base`) and
   is injective, so `c · h ^ 2 = f_S`;
6. hence `2 • divisor W h = single p 2` (`divisor_pow`, `divisor_algebraMap_base`), so
   `divisor W h = single p 1`;
7. which is impossible — `not_exists_divisor_eq_single_pointClosedPoint`
   (`DivisorPrincipality`, `#726`), *a single affine rational point is never a principal divisor*.

**`#E[2] = 4` enters at step 4 and nowhere else**, as the right-hand side of Artin's theorem inside
`finrank_fixedFieldTwo`, whose input is `card_torsionTwoMul` and hence `card_torsion_two` — the
roots of the `2`-division cubic, which does not go through Ward.  Ward (`#254`/`#258`/`#260`/`#261`)
gates `#E[n] = n²` at **general** `n` only, i.e. `#242`/`#251`.  So at `n = 2` the dependency the
old prose named is *discharged*, and what took its place was `hprin`, i.e. rung 5 (`#418`) — for
which see `NthRootOfPullback`.  ⚠️ Its own gate used to be the fibre description of `[2]∗`, `#639`
**rung 9** (`#774`, *not* `#701`, rung 8, which merely counts the fibre).  **Rung 9 is merged**
(`MulByTwoFibreInfinity`, then `MulByTwoFibreAffine`), and the class-group computation that was
then all that remained of it has since been run: ✅ **at `n = 2`, over an algebraically closed base
field, `hprin` is discharged** (`EllipticCurves.FunctionField.PullbackPrincipalityTwo`, `#791`),
which also carries the hypothesis-free rung-5 statement `exists_gS_two_of_isAlgClosed`.
`exists_gS_two` itself is unchanged and keeps `hprin`, because it is the general-field statement and
over an arbitrary `F` the gate is untouched.  At `n = 3` the position is different; see the `n = 3`
account below, which is the only place that says why.

So over `[IsAlgClosed F]` and `[W.IsElliptic]`, **no step of the list above is gated any longer** —
step 7's Dedekind hypothesis included.  ⚠️ That step is **not** something `[IsAlgClosed F]` buys:
`instIsDedekindDomain` (`CoordinateRingNormalGeneral`) supplies it for `[W.IsElliptic]` over any
field, so it is discharged before the algebraically-closed hypothesis is ever used, and it does not
belong on the list of what that hypothesis is needed for.  The assembly that was then all that
stood between the list and a theorem is
`EllipticCurves.FunctionField.WeilPairingNondegenerateTwo` (`#796`); it threads one `g_S` through
every `T`, which is what `weilPairingElt` taking `g_S` as an *argument*
(`weilPairingElt_eq_one_iff_translateEndo_fixed`) makes necessary, and it inherits the hypotheses
the ⚠️ below records.

⚠️ **"Non-degeneracy is proved" is true only over an algebraically closed base field**, where it
is `#796` at `n = 2` and `#831` at `n = 3`.  Over a general field at either `n` it is not, and for
general `n` this section remains an account of what non-degeneracy *consumes* rather than of a
theorem.

⚠️ **`#418` has two halves, and only the first one is on this path.**  `hprin`, the hypothesis of
`exists_gS_two`, asks that `divisor W ([2]∗ f)` be `2 •` a principal divisor; it mentions the
pullback of a *function* and no divisor-level `[n]∗` at all, so it is rung-4-independent.  The
other half of `#418`, `div g_S = [n]∗(S)`, does mention the divisor-level pullback, and it is what
the `#456` consumers (`GaloisPointAction`, `WeilPairingGaloisPoint`, `Galois/CyclotomicCharacter`)
mean by "rung 5 (`#418`), gated on `#421`/`#422`".  Both readings are correct about their own
statement; taking either for the other gives the wrong dependency picture, and non-degeneracy needs
only the first.

⚠️ **Step 4 carries `[IsAlgClosed F]`, and so does rung 9's fibre description** — `[W.IsElliptic]`
for the contraction-is-doubling statement, `[IsAlgClosed F]` on top of it for the count, the pinned
indices and the divisor identity — whereas this file carries `[W.IsElliptic]` and **not**
`[IsAlgClosed F]`.  `#791`'s discharge of `hprin` inherits the same hypothesis twice over, from the
fibre description and from the surjectivity of `[2]` on points (`exists_nsmul_two_eq`), which is why
it lands in its own module rather than weakening `exists_gS_two` in place.  "The count is merged"
and "the count is merged in the generality this theorem is stated in" are different claims; the
assembled non-degeneracy statement inherits `[IsAlgClosed F]`, which the `#418`/`#465` consumers
already carry but the `WeilPairing*` files do not — which is why `#796` lands in its own module too.

**At `n = 3` every step of the argument now has an analogue, and the gate is the same gate.**
Steps 1, 2, 5, 6 and 7 transpose (`exists_gS_three`, `mulByThreeEndo_algebraMap_base`), and steps 3
and 4 — which had no analogue at all when this section was first written — are
`mem_fixedFieldThree_iff` and `fixedFieldThree_eq_mulByThreeFieldRange`
(`EllipticCurves.FunctionField.MulByThreeGalois`, `#784`).  Artin's two sides under step 4 are
`finrank_mulByThreeFieldRange` (`MulByThreeDegree`, `#775`, by `#682`'s tower with `4 ↦ 9`) on the
left, and `card_torsionThreeMul` — hence `card_torsion_three`, likewise Ward-free —
(`TranslationActionThree`, `#783`) on the right.  So at `n = 3` too the gate is `hprin`, rung 5
(`#418`) — the **same** gate as at `n = 2`.

⚠️ **And it is now discharged at both `n`, over an algebraically closed base field.**
`EllipticCurves.FunctionField.PullbackPrincipalityTwo` did it at `n = 2` (`#791`) and
`EllipticCurves.FunctionField.PullbackPrincipalityThree` at `n = 3`, on top of
`EllipticCurves.FunctionField.MulByThreeFibre`'s `[3]∗(S) = ∑_{R ∈ E[3]} (P ⊕ R)`.  The asymmetry
that survived `#775`/`#783`/`#784` is therefore gone: what stands between `n = 3` and a rung-6
statement is not a gate but an absence of assembly.

**Assembled at `n = 3` over `F̄`.**  ⚠️ **This list is append-only, by construction** (`#843`).
When a slot lands, add one bullet naming its declaration, its module and its issue, and change
nothing else in this paragraph.  ⚠️ **Do not write a sentence about which slots are absent from
it** — a frontier claim of the form *"X and Y are the ones still unassembled"* is falsified by any
PR landing either, so every contributor edits the same clause.  That is not hypothetical: four
consecutive PRs rewrote this paragraph inside about two hours on 2026-08-23 and two of them
conflicted, docstring-only, at a full ROOT rebuild each.  A bullet list is only appended to.

* the **alternating property** — `exists_weilPairingElt_self_eq_one_of_isAlgClosed_three`
  (`EllipticCurves.FunctionField.WeilPairingAlternatingThreeAlgClosed`, `#829`).
* **Galois-equivariance** — `exists_weilPairingElt_galois_three`
  (`EllipticCurves.FunctionField.WeilPairingGaloisRoot`, `#830`).
* **non-degeneracy** — `exists_gS_three_weilPairingElt_ne_one`
  (`EllipticCurves.FunctionField.WeilPairingNondegenerateThree`, `#831`).
* the **`∀ g` root-independent form** —
  `exists_forall_weilPairingElt_self_eq_one_of_isAlgClosed_three`
  (`EllipticCurves.FunctionField.WeilPairingRootIndependenceAlgClosed`, `#836`, which discharged
  the same `hprin` at `n = 2` in the same file — ⚠️ that omission was symmetric, not an `n = 3`
  asymmetry).
* **antisymmetry**, in product form — `exists_weilPairingElt_mul_swap_eq_one_three`
  (`EllipticCurves.FunctionField.WeilPairingProductRelation`, `#845`).
* **antisymmetry in `μ_n(F)`** — `exists_weilPairingMu_mul_swap_eq_one_three`
  (`EllipticCurves.FunctionField.WeilPairingProductRelationMu`, `#855`).
* **antisymmetry for roots the caller supplies** —
  `weilPairingElt_mul_swap_eq_one_three_of_isAlgClosed`
  (`EllipticCurves.FunctionField.WeilPairingProductRelationRootIndependent`, `#854`; ⚠️ this one
  takes `g_S` and `g_T` as hypotheses instead of producing them, which is the point of that
  module, so it has an ordinary name and not an `exists_` one).
* **Galois-equivariance in `μ_n(F)`** — `exists_weilPairingMu_galois_three`
  (`EllipticCurves.FunctionField.WeilPairingGaloisRoot`, `#859`).
* **divisor-slot bilinearity** — `exists_weilPairingElt_divisorSlot_add_three`
  (`EllipticCurves.FunctionField.WeilPairingDivisorSlotBilinear`, `#861`).
* **translation-slot bilinearity** — `exists_weilPairingElt_translatePoint_add_three`
  (`EllipticCurves.FunctionField.WeilPairingTranslationSlotBilinear`, `#873`).
* **non-degeneracy in `μ_n(F)`** — `exists_gS_three_weilPairingMu_ne_one`
  (`EllipticCurves.FunctionField.WeilPairingNondegenerateMu`, `#878`).
* the **translation slot as a homomorphism** `E[3] → μ_3(F)` —
  `exists_weilPairingTorsionMuHom_three`
  (`EllipticCurves.FunctionField.WeilPairingTranslationSlotHom`, `#890`; ⚠️ this is the first
  rung-6 slot stated as a *map* out of the torsion group rather than pointwise, so its translation
  argument ranges over the point at infinity as well as the affine points).
* **non-degeneracy of that homomorphism** — `exists_weilPairingTorsionMuHom_three_ne_one`
  (`EllipticCurves.FunctionField.WeilPairingTranslationSlotNondegenerate`, `#893`; ⚠️ this is
  `#878`'s non-degeneracy with the affine witness quantified away, so it reads as `φ ≠ 1` rather
  than as an inequation at a named point).

⚠️ Over a **general** field `hprin` is still open at both `n`, and that is a different
statement from any of the above.  ⚠️ It is named here rather than bulleted above **because it does
not decay**: no slot landing over `F̄` makes it any less open, so it is safe to state as a standing
claim in a way that a count of assembled slots is not.

⚠️ The `n = 3` chain carries hypotheses in a shape the `n = 2` account never has to draw:
`finrank_mulByThreeFieldRange` needs `[W.IsElliptic]`, `(2 : F) ≠ 0` and `(3 : F) ≠ 0` but **no**
`[IsAlgClosed F]`, while `card_torsion_three` needs it — so the sandwich, and everything
`MulByThreeGalois` exports off it, carries the union.

## Naming: `_two` / `_three` track the **isogeny**, not the exponent

A `_two` or `_three` suffix on this front says which multiplication-by-`n` endomorphism the
statement is about — `mulByTwoEndo` versus `mulByThreeEndo` — and nothing else.  ⚠️ It does **not**
say the exponent is fixed: `weilPairingElt_pow_eq_one_of_gS_two` has a free `{n : ℕ}` and concludes
`e_n(S, T) ^ n = 1`, and its `n = 2`-ness lives entirely in the `mulByTwoEndo h2 f` on the right of
its rung-5 hypothesis.  A declaration can be general in the exponent and specific to the isogeny,
and most of the suffixed ones are.

⚠️ **An unsuffixed name therefore means "general in the isogeny", and that is now the only thing it
can mean.**  It used to mean that *or* "`n = 2`, written before anyone needed `n = 3`", with nothing
in the name to distinguish them; `#886` measured fifteen declarations carrying the second reading
and gave them their `_two`.  The names that are correctly bare are the ones that take the product
relation `hprod` as a hypothesis and mention no `mulBy*Endo` at all —
`weilPairingElt_divisorSlot_add` and `weilPairingMu_divisorSlot_add`, each of which has a `_two` and
a `_three` specialisation beside it.

⚠️ One pair is deliberately *not* on this scheme: `weilPairingElt_pow_eq_one_of_gS_torsion` and
`weilPairingElt_pow_eq_one_of_gS_two_torsion` are different theorems, not a bare/suffixed pair — the
first discharges `hcomm` from a `translatePoint`-level hypothesis and the second from a
`torsionPoint`-level one.  Reading the statement is what settles it, which is the general rule
whenever `_three` might be naming something other than an isogeny (`coeff_formalW_three` names the
coefficient index `3`).

⚠️ The convention is **checkable**, and the check is worth re-running whenever a family is added.
It is stated here rather than in a tracker thread because it has been reimplemented three times in
two days, and two of those implementations disagreed on their totals while agreeing on the only
bucket that matters.

Collect the **declaration names** in `EllipticCurves/**/*.lean` — every name introduced by a
`theorem`, `lemma`, `def`, `abbrev` or `instance`, taken as a set — and keep those matching the
token `_three(?=$|_|')`.  ⚠️ The lookahead is the point: `X_three'` does not end in `_three`, and
`_three` is not always terminal (`weilPairingElt_pow_eq_one_of_gS_three_torsion`).  Sort each into
**four** buckets by whether substituting `_two`, deleting the token, both, or neither yields a name
that also exists:

* **`_two` twin** — the convention working.
* **bare twin only** — the defect this section describes.  It should be empty but for
  `coeff_formalW`, whose `_three` indexes a coefficient.
* **both** — the collision guard.  If `X`, `X_two` and `X_three` all exist, renaming `X → X_two`
  collides rather than improves, so these must be left alone; the bucket reproduces this section's
  hand-written exceptions without curation.
* **neither** — genuinely `n = 3`-only.

⚠️ **The audit is a candidate generator and never a finding.**  Every candidate is settled by
reading the statement for `mulByTwoEndo` / `W.torsion 2` / `g ^ 2` / `(2 : F) ≠ 0`, which is what
separates a bare `n = 2` name from a `_three` that indexes something other than an isogeny.  ⚠️ And
report only the bare-twin bucket: the absolute totals have proved sensitive to how declarations are
collected, while the bare-twin bucket has reproduced across independent implementations.

⚠️ **Two differences in the collection step have been measured to move the totals, and the larger
is the identifier character class.**  A declaration name here may contain non-ASCII characters —
the division polynomials are `Ψ`, `Φ`, `Ω`, `ψ`, `φ` with `₀`–`₉` subscripts — so the pattern that
collects names must admit them.  ⚠️ The failure mode is **truncation, not omission**, which is why
it survives a glance at the regex: some of the affected names *begin* with a non-ASCII character,
but the rest begin with ASCII and are silently cut short at the first Greek letter, so
`exists_eval_Φ_three_eq` enters the set as `exists_eval_` — and the shortened string is what the
twin lookup then queries.  Twelve names move on this account, `Φ_three_eval`, `preΩ_three`,
`Ψ₃_eval_eq_zero_of_mem_torsion_three` and `natDegree_Φ_three_sub_C_mul_ΨSq_three` among them.
The second difference is the **declaration-keyword list**: dropping `def` and `abbrev` moves two
more.  ⚠️ Under all four combinations the **bare-twin bucket is unchanged**, which is the concrete
reason it is the only bucket worth reporting.

⚠️ **A second invariant, on the same footing and with the same kind of test: a declaration and its
twin belong in the same namespace.**  `#903` recorded that a namespace mismatch survives a clean
ROOT build, `mk_all`, a line-length check, a line-by-line read of the diff **and** a `#print axioms`
sweep — because every module on this front sits in `namespace WeierstrassCurve.Affine` with
`open CoordinateRing` and therefore resolves either spelling.  Its remedy has two halves, and
running only the first is what lets a breach through:

> print the new declaration's axioms **fully qualified**, *and* print the same for the declaration
> it claims to mirror.  If the prefixes differ, that is the finding.

The second half generalises to a check over every module at once.  Walk each file tracking
`namespace` and `end` as a stack, record each declaration's enclosing namespace, then for every name
ending `_of_hprin`, `_ne_one`, `_of_isAlgClosed`, `_of_algClosed` or `_baseChange` compare its
namespace with its base's.  ⚠️ Handle **both** suffix spellings — `X_of_hprin_{two,three}` mirrors
`X_{two,three}`, since `#910`'s review settled that *"mirror your twin" wins while every
`_of_hprin` file has a twin*, so the qualifier's position varies by design.  ⚠️ And use
`[^\s:({\[]+` for the name, never `[A-Za-z_]\w*`, for the truncation reason above.

⚠️ **The invariant is twin consistency, not a rule about the `exists_` prefix.**  The same stack
walk finds **eleven** `exists_` declarations inside `namespace CoordinateRing`, and all eleven
belong there on the merits.  Named, because a count on its own settles nothing and this paragraph
has been wrong twice for exactly that reason:

* the ring, its units and its places — `exists_eq_algebraMap_of_isUnit`, `exists_deg_eq`,
  `exists_deg_sub_lt`, `exists_eq_algebraMap_of_deg_eq_zero`,
  `exists_equation_and_eq_XYIdeal_of_isMaximal`, `exists_generator_divisor_galois`,
  `exists_unit_galoisFunctionField_of_smul_pow` and the two
  `exists_{scalar,unit}_galoisFunctionField_of_divisor_eq`;
* `exists_algebraMap_of_pow_eq_one`, about the **function field** rather than the ring — an `n`-th
  root of unity in `F(W)` is a constant — which sits here because `F(W)` is `F[W]`'s fraction
  field, not because it is a ring statement;
* `exists_leadingCoeff_ratio`, a `private` `F[X]` degree lemma feeding `exists_deg_sub_lt`, which
  is a statement about neither.  ⚠️ It is in the count because the stack walk collects `private`
  declarations too — worth knowing before comparing totals with an implementation that does not.

⚠️ **It read nineteen until `#927`**, the extra eight being rung-6 *headlines* —
`exists_weilPairing{Elt,Mu}_galois_{two,three}` (`WeilPairingGaloisRoot`) and their `_of_hprin`
twins (`WeilPairingGaloisRootHprin`, `#923`) — which on the house pattern were all out of place, the
`_of_hprin` four only because their twins were.  `#927` moved all eight up to `Affine` in one PR,
which is the only way to move any of them: this check sees a twin *pair* straddling two namespaces,
so moving one file's four alone takes it from 0 to 4.  ⚠️ **That is the shape of every fix to this
particular defect — the mechanical invariant and the house pattern can each be satisfied alone, and
only a simultaneous move satisfies both.**

⚠️ **Before that, this paragraph said "fifteen … correctly placed, because they are statements about
the coordinate ring and its places", and that was wrong before either of the two 2026-08-23 merges
touched the tree** — the fifteen already included `WeilPairingGaloisRoot`'s four headlines, which
are not such statements.  The error was to name four genuine examples and generalise them to the
whole count.  ⚠️ **A census is only as good as its enumeration: list the members or state the split,
never a bare total with an explanation attached.**

What the house pattern asks (`WeilPairingRootIndependence` demonstrates it) is that the **lemma
layer** sits in `CoordinateRing` and the `exists_` **headlines** one level up; what this check
enforces is only that a twin pair does not straddle the two.  ⚠️ **So a fix that satisfies the check
can still be wrong** — `#918` moved four declarations where only two had a mismatched twin, because
moving the two alone would have split `exists_weilPairingTorsionMuHom_two` from its `_ne_one`
sibling, a defect one name over that the check does not see.  Reading the file is still what settles
placement.  The check has found exactly one breach so far, `#873`'s bundled-hom pair against
`#913`'s, repaired by `#918`, and reports **0** as of `#927` — which was a placement fix that did
*not* start from a breach: the eight it moved had matching twins throughout, and it is the
`exists_`-in-`CoordinateRing` column, not the mismatch column, that flagged them.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.
-/

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-- **The Weil-pairing element** `e_n(S, T) := τ_T∗(g_S) / g_S ∈ F(W)`.

Here `g = g_S` is the `n`-th root of the pulled-back principal function of `S` (rung 5) and
`h₂ : W.Equation x₂ y₂` encodes the translation point `T = (x₂, y₂)` via `translateEndo h₂`. -/
noncomputable def weilPairingElt {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) (g : W.FunctionField) :
    W.FunctionField :=
  translateEndo h₂ g / g

/-- The Weil-pairing element is nonzero whenever `g_S` is (the translation endomorphism is
injective, so `τ_T∗(g_S) ≠ 0`, and the quotient of two nonzero elements is nonzero). -/
theorem weilPairingElt_ne_zero {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {g : W.FunctionField}
    (hg : g ≠ 0) : weilPairingElt h₂ g ≠ 0 := by
  have hinj : Function.Injective (translateEndo h₂) := RingHom.injective _
  rw [weilPairingElt]
  exact div_ne_zero ((map_ne_zero_iff _ hinj).mpr hg) hg

/-- **`e_n(S, T)` is an `n`-th root of unity.** Given that the translation fixes `g_S ^ n`
(`translateEndo h₂ (g ^ n) = g ^ n`), the pairing value satisfies `e_n(S, T) ^ n = 1`:
`(τ_T∗ g / g) ^ n = τ_T∗(g ^ n) / g ^ n = g ^ n / g ^ n = 1`. -/
theorem weilPairingElt_pow_eq_one {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {g : W.FunctionField}
    (hg : g ≠ 0) {n : ℕ} (hfix : translateEndo h₂ (g ^ n) = g ^ n) :
    weilPairingElt h₂ g ^ n = 1 := by
  rw [weilPairingElt, div_pow, ← map_pow, hfix, div_self (pow_ne_zero n hg)]

/-- **The translation fixes `g_S ^ n`.** From the rung-5 datum `u · g ^ n = h` (with `h = [n]∗ f_S`
the pulled-back principal function and `u` a unit of `F[W]`), together with the two inputs

* `hcomm : translateEndo h₂ h = h` — the commuting identity `[n](P + T) = [n]P`, and
* `huf`   : the translation fixes the constant unit `u`,

the translation fixes `g ^ n`.  Applying `translateEndo h₂` to `u · g ^ n = h` and cancelling the
nonzero factor `algebraMap u` gives `translateEndo h₂ (g ^ n) = g ^ n`. -/
theorem translateEndo_pow_eq_self_of {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    {g h : W.FunctionField} {u : W.CoordinateRingˣ} {n : ℕ}
    (hu : (u : W.CoordinateRing) • g ^ n = h)
    (hcomm : translateEndo h₂ h = h)
    (huf : translateEndo h₂ (algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing))
      = algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing)) :
    translateEndo h₂ (g ^ n) = g ^ n := by
  have hsmul : algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing) * g ^ n = h := by
    rw [← Algebra.smul_def]; exact hu
  have hA : algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective W.CoordinateRing W.FunctionField)]
    exact u.ne_zero
  have key : algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing) *
      translateEndo h₂ (g ^ n) =
      algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing) * g ^ n := by
    have hcong := congrArg (translateEndo h₂) hsmul
    rw [map_mul, huf, hcomm] at hcong
    exact hcong.trans hsmul.symm
  exact mul_left_cancel₀ hA key

/-- **The translation fixes every unit of `F[W]` (`huf` discharged).**  The unit `u` produced by the
rung-5 construction is a unit of the affine coordinate ring, hence a nonzero constant
(`exists_eq_algebraMap_of_isUnit`), and `translateEndo` — being an `F`-algebra homomorphism
(`translateCoordHom_algebraMap`) — fixes constants.  This discharges the `huf` hypothesis of
`translateEndo_pow_eq_self_of` unconditionally, for any unit `u`. -/
theorem translateEndo_algebraMap_unit {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    (u : W.CoordinateRingˣ) :
    translateEndo h₂ (algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing))
      = algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing) := by
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_isUnit u.isUnit
  rw [hc, translateEndo_algebraMap, translateCoordHom_algebraMap,
    ← IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField]

/-- **`e_n(S, T) ^ n = 1` from the rung-5 datum and the two named inputs.** Combines
`translateEndo_pow_eq_self_of` (which produces `translateEndo h₂ (g ^ n) = g ^ n`) with
`weilPairingElt_pow_eq_one`.  Here `h = [n]∗ f_S = mulByTwoEndo h2 f` and `g = g_S`. -/
theorem weilPairingElt_pow_eq_one_of_gS_two {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) (h2 : (2 : F) ≠ 0)
    {f g : W.FunctionField} {u : W.CoordinateRingˣ} {n : ℕ} (hg : g ≠ 0)
    (hu : (u : W.CoordinateRing) • g ^ n = mulByTwoEndo h2 f)
    (hcomm : translateEndo h₂ (mulByTwoEndo h2 f) = mulByTwoEndo h2 f)
    (huf : translateEndo h₂ (algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing))
      = algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing)) :
    weilPairingElt h₂ g ^ n = 1 :=
  weilPairingElt_pow_eq_one h₂ hg (translateEndo_pow_eq_self_of h₂ hu hcomm huf)

/-- **`e_n(S, T) ^ n = 1`, concrete `n = 3` instance.** The `mulByThreeEndo` analogue of
`weilPairingElt_pow_eq_one_of_gS_two`: here the pulled-back principal function is
`h = [3]∗ f_S = mulByThreeEndo h2 h3 f` and `g = g_S` is the rung-5 `n = 3` root
(`exists_gS_three`, `u · g ^ 3 = mulByThreeEndo h2 h3 f`).  Nothing in the reduction is specific to
`n = 2`: `translateEndo_pow_eq_self_of` and `weilPairingElt_pow_eq_one` are `n`-agnostic, so the two
named inputs `hcomm`/`huf` are supplied on the `mulByThreeEndo` datum and the same cancellation
produces `e_n(S, T) ^ n = 1`. -/
theorem weilPairingElt_pow_eq_one_of_gS_three {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {f g : W.FunctionField} {u : W.CoordinateRingˣ} {n : ℕ} (hg : g ≠ 0)
    (hu : (u : W.CoordinateRing) • g ^ n = mulByThreeEndo h2 h3 f)
    (hcomm : translateEndo h₂ (mulByThreeEndo h2 h3 f) = mulByThreeEndo h2 h3 f)
    (huf : translateEndo h₂ (algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing))
      = algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing)) :
    weilPairingElt h₂ g ^ n = 1 :=
  weilPairingElt_pow_eq_one h₂ hg (translateEndo_pow_eq_self_of h₂ hu hcomm huf)

/-- **`e_n(S, T) ^ n = 1` from the rung-5 datum and `hcomm` alone (`n = 2`).**  The `huf` hypothesis
of `weilPairingElt_pow_eq_one_of_gS_two` is now discharged by `translateEndo_algebraMap_unit`
(the unit `u` is a constant), leaving only the geometric commuting identity `hcomm`
(`[n](P + T) = [n]P`). -/
theorem weilPairingElt_pow_eq_one_of_gS_two' {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) (h2 : (2 : F) ≠ 0)
    {f g : W.FunctionField} {u : W.CoordinateRingˣ} {n : ℕ} (hg : g ≠ 0)
    (hu : (u : W.CoordinateRing) • g ^ n = mulByTwoEndo h2 f)
    (hcomm : translateEndo h₂ (mulByTwoEndo h2 f) = mulByTwoEndo h2 f) :
    weilPairingElt h₂ g ^ n = 1 :=
  weilPairingElt_pow_eq_one_of_gS_two h₂ h2 hg hu hcomm (translateEndo_algebraMap_unit h₂ u)

/-- **`e_n(S, T) ^ n = 1` from the rung-5 datum and `hcomm` alone (`n = 3`).**  The `mulByThreeEndo`
analogue of `weilPairingElt_pow_eq_one_of_gS_two'`; `huf` is discharged by
`translateEndo_algebraMap_unit`, leaving only `hcomm`. -/
theorem weilPairingElt_pow_eq_one_of_gS_three' {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {f g : W.FunctionField} {u : W.CoordinateRingˣ} {n : ℕ}
    (hg : g ≠ 0) (hu : (u : W.CoordinateRing) • g ^ n = mulByThreeEndo h2 h3 f)
    (hcomm : translateEndo h₂ (mulByThreeEndo h2 h3 f) = mulByThreeEndo h2 h3 f) :
    weilPairingElt h₂ g ^ n = 1 :=
  weilPairingElt_pow_eq_one_of_gS_three h₂ h2 h3 hg hu hcomm (translateEndo_algebraMap_unit h₂ u)

end CoordinateRing

end WeierstrassCurve.Affine
