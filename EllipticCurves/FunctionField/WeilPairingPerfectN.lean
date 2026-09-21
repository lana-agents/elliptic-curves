/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairingFunctionN
import EllipticCurves.FunctionField.WeilPairingPerfect

/-!
# The Weil pairing is perfect at a general `n`: `E[n]` is its own dual

`EllipticCurves.FunctionField.WeilPairingPerfect` (`#940`) proves that `S ↦ e_n(S, ·)` is a
bijection from `E[n]` onto its dual group at `n = 2` and at `n = 3`, and its
`## Explicitly out of scope` says in terms what would remove the restriction:

> `#938`'s surjectivity argument runs through a group of *prime* order and has no analogue at
> composite `n`; Mathlib's duality is stated for an arbitrary finite abelian group, so the argument
> in this file would transcribe unchanged to any `n` for which `weilPairingNHom` and
> `ker_weilPairingNHom` existed.

`EllipticCurves.FunctionField.WeilPairingFunctionN` (`#2030`) built both.  **This file is that
transcription, and the sentence above is its whole proof strategy.**

## What the transcription actually costs, measured rather than estimated

⚠️ **Three of the four inputs of the merged `n = 2` and `n = 3` proofs are already general in `n`,
are public, and are not restated here.**  All three live in `WeilPairingPerfect`:

* `monoidHomRootsOfUnityEquiv {n : ℕ} (hG : ∀ g : G, g ^ n = 1)` — root namespace, a statement about
  a group and a field and nothing else;
* `natCard_monoidHom_rootsOfUnity (hn : (n : F) ≠ 0) (hG : ∀ g, g ^ n = 1)` — the duality count,
  likewise curve-free.  ⚠️ The exponent of `E[n]` is never computed: `HasEnoughRootsOfUnity.of_dvd`
  turns `∀ g, g ^ n = 1` into the instance Mathlib's duality theorem wants;
* `WeierstrassCurve.Affine.pow_eq_one_multiplicative_torsion {n : ℕ}` — two lines, general in `n`,
  over an arbitrary field, with no elliptic hypothesis.

The fourth is finiteness of `E[n]`, and that is the only place the numeral proofs are numeral-bound:
they call `finite_torsion_two` / `finite_torsion_three`.

⚠️ **`#2031`'s description spiked a new `finite_torsion_n` here, derived from
`card_torsion_eq_sq`, and it is NOT declared — the general lemma was already on `main` and it is
strictly weaker in hypotheses.**  `EllipticCurves.Torsion.XSupport`'s
`finite_torsion_of_intCast_ne_zero (h2 : (2 : F) ≠ 0) (hn : (n : F) ≠ 0) : Finite (W.torsion n)`
holds over an **arbitrary** field with **no** `[IsAlgClosed F]` and **no** `[W.IsElliptic]`, and it
does not spend a torsion count at all — it runs off `finite_torsionXSupport`.  The spiked version
would have bought the same instance for `card_torsion_eq_sq` plus two instances.  ⚠️ That check is
the one the issue asked for in terms (*"Check whether a `Finite` instance for `W.torsion n` at a
general index already exists before declaring it"*), and it is `#868`'s pattern, which this front
has paid for four times.

**So the diff against the merged `n = 2` bodies is one line per proof**: `W.finite_torsion_two h2`
becomes `W.finite_torsion_of_intCast_ne_zero h2 hnF`.  Every other token below is
`WeilPairingPerfect`'s, index letter for numeral.

## The setting, once, so that the reach clauses below can defer to it

The span these clauses defer to is the **four** public declarations of `### The perfect pairing at
a general `n``.  ⚠️ `### Non-vacuity` is outside it, being stated over a named field rather than
over the variable `F`.  All four carry `[IsAlgClosed F]`, `[W.IsElliptic]`, `(2 : F) ≠ 0` and
`((n : ℤ) : F) ≠ 0`; **three** of the four also carry `[NeZero n]`, and the one that does not is
`natCard_monoidHom_torsionN`, whose statement mentions neither `weilPairingNHom` nor
`weilPairingN`.  That is `WeilPairingFunctionN`'s setting exactly, and **not one hypothesis more**.

⚠️ **`[NeZero n]` is forced and not chosen** on the three that bind it, for the reason
`WeilPairingFunctionN` gives for its own fifteen: `weilPairingNHom` elaborates through
`rootsOfUnity n F`, which does not elaborate without it.

## Main statements

**The hypotheses the bullets below omit** are the four of the setting paragraph above, plus
`[NeZero n]` on the first three.

* `WeierstrassCurve.Affine.bijective_weilPairingNHom` : **`S ↦ e_n(S, ·)` is a bijection from
  `E[n]` onto `Multiplicative E[n] →* μ_n(F̄)`** — the headline, and the general-`n` form of
  `bijective_weilPairing{Two,Three}Hom`.  ⚠️ The number `n²` is **not** used: the count is
  `#(G →* μ_n) = #G` for the *same* `G` on both sides, exactly as at `n = 2` and `n = 3`.
* `WeierstrassCurve.Affine.weilPairingNEquiv` : the same bundled as `E[n] ≃* E[n]^∨`.
* `WeierstrassCurve.Affine.existsUnique_weilPairingNHom_eq` : **every character of `E[n]` is
  `e_n(S, ·)` for exactly one `S`** — the reading a consumer quotes, with no `MulEquiv` to unfold.
* `WeierstrassCurve.Affine.natCard_monoidHom_torsionN` : **`#E[n]^∨ = n²`**.  ⚠️ This is the one
  statement here that consumes `card_torsion_eq_sq` (`#242`/`#293`,
  `EllipticCurves.Torsion.StructureGeneral`); the three above it do not, which is why it is the
  load-bearing certificate in `### Non-vacuity` below and they are not.

## Naming and placement

`WeierstrassCurve.Affine` with `open CoordinateRing`, `#903`'s house pattern as enforced by `#918`
and `#927`.  The `_n` / `N` index slot is the one `_two` and `_three` occupy in
`WeilPairingPerfect`, and the four names are that file's four with the numeral replaced.
⚠️ **Nothing here is at the root namespace**: the two curve-free declarations of
`WeilPairingPerfect` are already general in `n` and are consumed, not mirrored.

## Scope

⚠️ **`WeilPairingPerfect`'s `General n` bullet is edited by this commit and its quoted sentence is
not.**  That bullet's *"the argument in this file would transcribe unchanged to any `n` for which
`weilPairingNHom` and `ker_weilPairingNHom` existed"* was true when written and is true now; what
`#2030` added beneath it — *"what is still absent is the transcription itself"* — is what this
landing falsifies, and it is repaired there rather than left standing.  ⚠️ This is the `#1982`
class: an absence claim in a file this work does not otherwise touch.

⚠️ **`WeilPairingNondegenerateN`'s `## Scope` is read and deliberately NOT edited**, and the reason
is the sentence rather than the name.  It says *"Perfectness at `n = 2, 3` is
`bijective_weilPairing{Two,Three}Hom` …; nothing here narrows the distance to a general-`n` form of
it."*  The first clause is **scoped to `n = 2, 3` in its own words** and is still an exact account
of those two indices; the second is scoped to *that file*, which still narrows nothing.  Neither
is a claim that perfectness lives nowhere else, so neither goes stale.  ⚠️ Editing it would be the
duplicate-pointer shape `#1960` files.

⚠️ **The arbitrary-field form is false and not merely absent.**  Over a non-closed `F` the dual
group is smaller than `E[n]` and the map is not onto — `[IsAlgClosed F]` is doing the
`HasEnoughRootsOfUnity F n` job here, which is the second, independent thing it does on this front.
There is nothing to lift, and this is inherited verbatim from `#938` through `WeilPairingPerfect`.

⚠️ **The statements below are pinned to `Classical.propDecidable`**, as every file on this front is:
`open Classical in` is required, not decorative, because `TorsionNMul` bakes the classical
`DecidableEq F` instance in and the statements mention `W.torsion n`.

## Explicitly out of scope

* **The double dual.**  `CommGroup.monoidHomMonoidHomEquiv` would compose with `weilPairingNEquiv`
  in one line; there is no consumer, so it is absent on purpose — `WeilPairingPerfect`'s own reason,
  unchanged.
* **Galois-equivariance of the equiv.**  `#936` left bundled-hom equivariance unfiled for want of a
  consumer and that reasoning is unchanged here.
* **Deprecating, restating or touching `WeilPairingPerfect`'s `n = 2` and `n = 3` statements.**
  `#1304`'s and `#1308`'s rule: at those two indices the merged ones are still the right thing to
  cite, their proofs being shorter and routed through `ker_weilPairing{Two,Three}Hom` directly.
  ⚠️ **And they are not corollaries of the four below** — `weilPairingTwoHom` and `weilPairingNHom`
  are different constructions, and `WeilPairingFunctionN`'s
  `### Recovery of the merged numeral layers, compiled` is what relates them; recovering
  `bijective_weilPairingTwoHom` from `bijective_weilPairingNHom` would need that bridge and has no
  consumer.
* **`E[n] ≅ (ℤ/nℤ)²`** — `#242`/`#293`, a different statement.  ⚠️ Unlike `WeilPairingPerfect`,
  which deliberately does *not* route through it, this file **does** consume its cardinality
  corollary, and in exactly one declaration; see `## Main statements`.

## Non-vacuity

⚠️ **The certificate index is `5`, and it is chosen rather than convenient.**
`EllipticCurves.Torsion.ThreePrimary`'s `nonempty_torsion_addEquiv_zmod_sq_of_smooth` says
*"the first index it does not cover is `n = 5`"* — of **itself**, its `3`-smooth statements being
what stops there — and `EllipticCurves.Torsion.StructureGeneral` quotes that sentence, attributed,
in the very section where it declares `card_torsion_five` and `nonempty_torsionFive_addEquiv`.
⚠️ **The two files must not be swapped here, and the pronoun is why**: `StructureGeneral` is
precisely the file that *does* cover `n = 5`, so re-attributing the sentence to it would say of
that file the opposite of what it says of itself.  `5` is therefore the first index the `3`-smooth
statements stop at **and** the first one the general statements reach.  `n = 2` and `n = 3` are the
two `WeilPairingPerfect` already certifies — so a certificate at either of those would demonstrate
nothing this tree did not have.
The curve is the shared `EllipticCurves.Fixture.y2EqX3SubX` over
`EllipticCurves.Fixture.AlgClosedQ`.

⚠️ **The load-bearing certificate is the numeric one**, `#916`'s rule: the bijectivity and `∃!`
statements are schematic — they name no number and have no argument to degenerate — while
`Nat.card (Multiplicative E[5] →* μ_5) = 25` is false at every other value, consumes
`card_torsion_eq_sq` on top of the duality count, and is not provable by `rfl`.  The refutation twin
below is `WeilPairingPerfect`'s own device for the schematic half: the *same* claim about the
*trivial* bilinear map on the *same* curve is **false**, because `E[5]` has twenty-five elements and
a constant map is not injective.

## References

Silverman, *The Arithmetic of Elliptic Curves*, III.8.1 — read off page 94 of the 2nd edition,
where (b) is the alternating property and (c) is non-degeneracy (`#1001`).  The perfect-pairing
reading is the standard consequence of (c) over an algebraically closed field, and the duality half
is Mathlib's `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity`.
-/

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [IsAlgClosed F] [W.IsElliptic]

/-! ### The perfect pairing at a general `n` -/

open Classical in
/-- **The Weil pairing is perfect at a general `n`**: `S ↦ e_n(S, ·)` is a bijection from `E[n]`
onto its dual group `Multiplicative E[n] →* μ_n(F̄)`.

Injectivity is `ker_weilPairingNHom` (`#2030`).  The two sides have the same finite cardinality by
`natCard_monoidHom_rootsOfUnity`, which is where Mathlib's finite-abelian duality enters.
⚠️ The number `n²` is not used: the count is `#(G →* μ_n) = #G` for the same `G` on both sides.
⚠️ Finiteness of `E[n]` is `finite_torsion_of_intCast_ne_zero`, which needs neither
`[IsAlgClosed F]` nor `[W.IsElliptic]` and spends no torsion count. -/
theorem bijective_weilPairingNHom (h2 : (2 : F) ≠ 0) {n : ℕ} [NeZero n]
    (hn : ((n : ℤ) : F) ≠ 0) :
    Function.Bijective (weilPairingNHom (W := W) h2 hn) := by
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
  haveI := W.finite_torsion_of_intCast_ne_zero h2 hnF
  haveI : Finite (Multiplicative (W.torsion n)) := inferInstanceAs (Finite (W.torsion n))
  have hcard : Nat.card (Multiplicative (W.torsion n) →* rootsOfUnity n F)
      = Nat.card (Multiplicative (W.torsion n)) :=
    natCard_monoidHom_rootsOfUnity hnF pow_eq_one_multiplicative_torsion
  haveI : Finite (Multiplicative (W.torsion n) →* rootsOfUnity n F) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  exact (Nat.bijective_iff_injective_and_card _).mpr
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (ker_weilPairingNHom h2 hn), hcard.symm⟩

open Classical in
/-- **`E[n] ≅ E[n]^∨` at a general `n`**, the perfect pairing bundled as a group isomorphism onto
the dual. -/
noncomputable def weilPairingNEquiv (h2 : (2 : F) ≠ 0) {n : ℕ} [NeZero n]
    (hn : ((n : ℤ) : F) ≠ 0) :
    Multiplicative (W.torsion n) ≃* (Multiplicative (W.torsion n) →* rootsOfUnity n F) :=
  MulEquiv.ofBijective _ (bijective_weilPairingNHom h2 hn)

open Classical in
/-- **Every character of `E[n]` is `e_n(S, ·)` for exactly one `S`** — the reading of perfectness a
consumer quotes, with no `MulEquiv` to unfold. -/
theorem existsUnique_weilPairingNHom_eq (h2 : (2 : F) ≠ 0) {n : ℕ} [NeZero n]
    (hn : ((n : ℤ) : F) ≠ 0) (φ : Multiplicative (W.torsion n) →* rootsOfUnity n F) :
    ∃! S : Multiplicative (W.torsion n), weilPairingNHom h2 hn S = φ :=
  (bijective_weilPairingNHom h2 hn).existsUnique φ

open Classical in
/-- **`#E[n]^∨ = n²`.**  ⚠️ This is the one statement in this file that consumes
`card_torsion_eq_sq`; the perfect-pairing theorem above does not.  ⚠️ It binds no `[NeZero n]`:
`rootsOfUnity n F` is the only thing that needs it and this statement reaches it through
`Nat.card`, which is total. -/
theorem natCard_monoidHom_torsionN (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0) :
    Nat.card (Multiplicative (W.torsion n) →* rootsOfUnity n F) = n ^ 2 := by
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
  haveI := W.finite_torsion_of_intCast_ne_zero h2 hnF
  haveI : Finite (Multiplicative (W.torsion n)) := inferInstanceAs (Finite (W.torsion n))
  rw [natCard_monoidHom_rootsOfUnity hnF pow_eq_one_multiplicative_torsion,
    Nat.card_congr Multiplicative.toAdd, card_torsion_eq_sq h2 hnF]

/-! ### Non-vacuity -/

section Nonvacuity

/-! The certificate curve `y² = x³ − x` is the shared `EllipticCurves.Fixture.y2EqX3SubX`, and the
base — algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `5 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here. -/

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleFive : (((5 : ℕ) : ℤ) : AlgClosedQ) ≠ 0 := by norm_num

private lemma exampleFiveF : ((5 : ℕ) : AlgClosedQ) ≠ 0 := by norm_num

open Classical in
/-- The pairing on `y² = x³ − x` identifies `E[5]` with its dual — an index neither merged numeral
file reaches, and the weightless certificate, which this block says rather than presenting it as
more. -/
example : Function.Bijective
    (weilPairingNHom (W := y2EqX3SubX AlgClosedQ) exampleTwo exampleFive) :=
  bijective_weilPairingNHom exampleTwo exampleFive

open Classical in
/-- Every character of `E[5]` on that curve is `e_5(S, ·)` for exactly one `S`. -/
example (φ : Multiplicative ((y2EqX3SubX AlgClosedQ).torsion 5) →* rootsOfUnity 5 AlgClosedQ) :
    ∃! S : Multiplicative ((y2EqX3SubX AlgClosedQ).torsion 5),
      weilPairingNHom exampleTwo exampleFive S = φ :=
  existsUnique_weilPairingNHom_eq exampleTwo exampleFive φ

open Classical in
/-- **⚠️ The load-bearing certificate**: the dual of `E[5]` on `y² = x³ − x` has exactly twenty-five
elements.  Named number, supplied by `card_torsion_eq_sq` on top of the duality count, not provable
by `rfl`, and at an index outside the `3`-smooth range and outside both merged numeral files. -/
example :
    Nat.card (Multiplicative ((y2EqX3SubX AlgClosedQ).torsion 5) →* rootsOfUnity 5 AlgClosedQ)
        = 25 := by
  rw [natCard_monoidHom_torsionN exampleTwo exampleFive]; norm_num

open Classical in
/-- **⚠️ Why the bijectivity certificate above is not weightless**: the *same* claim about the
*trivial* bilinear map on the *same* curve is false, because `E[5]` has twenty-five elements and a
constant map is not injective.  This is a refutation checked by the build, not a failed proof
attempt.  ⚠️ It consumes `card_torsion_five` — the *named* `#E[5] = 25` instance
`Torsion.StructureGeneral` declares in the section quoted above, *"so that they are consumed if
anything downstream wants a concrete instance"*: its own words, and that file italicises *consumed*
inside the span.  The numeric certificate above instead goes through the duality count and
`card_torsion_eq_sq` directly, so the two certificates in this block differ in the declaration each
CONSUMES and not in what they REST ON: `card_torsion_five` is itself `card_torsion_eq_sq` plus
`norm_num`, three lines of `StructureGeneral`, so a defect in that count would take both and
neither is independent confirmation of the other.  This is the first downstream consumer of the
named instance. -/
private theorem not_bijective_one_five :
    ¬ Function.Bijective
      (1 : Multiplicative ((y2EqX3SubX AlgClosedQ).torsion 5) →*
        Multiplicative ((y2EqX3SubX AlgClosedQ).torsion 5) →* rootsOfUnity 5 AlgClosedQ) := by
  intro hbij
  haveI := (y2EqX3SubX AlgClosedQ).finite_torsion_of_intCast_ne_zero exampleTwo exampleFiveF
  have hcard : Nat.card (Multiplicative ((y2EqX3SubX AlgClosedQ).torsion 5)) = 25 := by
    rw [Nat.card_congr Multiplicative.toAdd]
    exact card_torsion_five exampleTwo exampleFiveF
  haveI hsub : Subsingleton (Multiplicative ((y2EqX3SubX AlgClosedQ).torsion 5)) :=
    ⟨fun a b => hbij.injective (by simp)⟩
  rw [Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩] at hcard
  exact absurd hcard (by norm_num)

end Nonvacuity

end WeierstrassCurve.Affine
