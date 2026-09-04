/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.WeilPairingSurjective
import EllipticCurves.FunctionField.WeilPairingTranslationSlotNondegenerate

/-!
# `e_n(S, ·) : E[n] → μ_n(F̄)` is **never** injective, at `n = 2` and `n = 3`

`EllipticCurves.FunctionField.WeilPairingTranslationSlotNondegenerate` (`#893`) proves that the
bundled translation slot

```lean
weilPairingTorsionMuHom_two h2 hgS hu : Multiplicative (W.torsion 2) →* rootsOfUnity 2 F
```

is **not the trivial homomorphism** — that is what non-degeneracy says about the map, and it is
sharp.  Its `## Scope` section then listed *injectivity* of the same map as out of scope and
`#242`-gated through `#E[n] = n²`.

⚠️ **That was wrong, and wrong in an unusual direction: the theorem it named as the gate is the
theorem that refutes the statement.**  Over an algebraically closed base field `#E[n] = n²` is
merged at both `n` (`card_torsion_two`, `card_torsion_three`) and `#μ_n(F̄) = n` is merged too
(`natCard_rootsOfUnity_of_ne_zero`), so the source of the map has `n²` elements and its target has
`n`.  For `n ≥ 2` there is no injection at all.  **Injectivity here is not open; it is false**, and
this file records that as a theorem rather than leaving a false gate standing.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.not_injective_weilPairingTorsionMuHom_two` and
  `…_three` — the map is not injective over a field with `(2 : F) ≠ 0`, and `(3 : F) ≠ 0` as well
  at `n = 3`, for **every** `S`, every rung-5 root and every certificate;
* `WeierstrassCurve.Affine.CoordinateRing.ker_weilPairingTorsionMuHom_two_ne_bot` and `…_three_…` —
  the same statement about the kernel, in the shape
  `EllipticCurves.FunctionField.WeilPairingTranslationSlotNondegenerate`'s
  `ker_weilPairingTorsionMuHom_two_ne_top` is written.

## ⚠️ Nothing here says the pairing is weaker than advertised

The two statements a reader might confuse are genuinely different, and **the strong one is true**:

* `e_n(S, ·)` for a **fixed** `S` is a map `E[n] → μ_n(F̄)` between groups of sizes `n²` and `n`.
  Non-degeneracy is `e_n(S, ·) ≠ 1` for `S ≠ O`, and that is proved as
  `weilPairingTorsionMuHom_two_ne_one` in
  `EllipticCurves.FunctionField.WeilPairingTranslationSlotNondegenerate`.  Injectivity is refuted
  by `not_injective_weilPairingTorsionMuHom_two`.  ⚠️ And on the *canonical* root — the
  root-independent form `weilPairingTwo h2 S`, which is a different object from
  `weilPairingTorsionMuHom_two h2 hgS hu` at an arbitrary `gS` — strictly more is known: for
  `S ≠ O` the map is **onto** `μ_2(F̄)` (`weilPairingTwo_surjective`,
  `EllipticCurves.FunctionField.WeilPairingSurjective`, `#938`).  A surjection from a group of
  order `n²` onto one of order `n` cannot be injective, so on that form the refutation is not even
  a separate fact; this file's statements are the ones that hold at *every* root, where
  surjectivity is not available.
* `S ↦ e_n(S, ·)`, the map into the **dual group** `E[n] →* μ_n(F̄)`, *is* injective, and in fact
  bijective: `bijective_weilPairingTwoHom` / `bijective_weilPairingThreeHom`
  (`EllipticCurves.FunctionField.WeilPairingPerfect`, `#940`).  That is the perfect-pairing
  statement, and it is where "the Weil pairing is non-degenerate" has its strongest formal content
  on this front.

⚠️ **The refuted statement is the one about a fixed `S`; the true one is about the slot map.**  A
clause that calls the first "gated" reads as though the pairing might one day be sharper than it
is.

## The proof, and the standard reason it does not use

Both proofs are the counting argument and nothing else: an injection `α ↪ β` between finite types
forces `Nat.card α ≤ Nat.card β` (`Nat.card_le_card_of_injective`, with the `Finite` instance for
`rootsOfUnity` coming from Mathlib), and `4 ≤ 2` / `9 ≤ 3` is false.  The `Multiplicative`
type-synonym transport is one rewrite, `Nat.card_congr Multiplicative.toAdd`, which is the idiom
`EllipticCurves.FunctionField.WeilPairingPerfect`'s `not_bijective_one_two` already uses.

⚠️ The *conceptual* reason for the failure is different and is deliberately not what is formalised
here: `e_n(S, S) = 1`, so for an `F`-rational `S` of order `n ≥ 2` the subgroup `⟨S⟩` lies in the
kernel and injectivity fails over **any** base field, closed or not.  ⚠️ **That argument needs such
an `S`, and the statements below name none** — see `## Scope`.  This tree does prove that
alternating identity, but only in an
`∃`-shape that produces its own root and certificate
(`exists_weilPairingMu_self_eq_one_of_isAlgClosed_two`,
`EllipticCurves.FunctionField.WeilPairingAlternatingTwoAlgClosed`), so it cannot be applied to the
arbitrary `hgS`/`hu` the statements below quantify over.  **Saying which argument is used and which
is merely true is the point**: the counting proof needs `[IsAlgClosed F]` and the group-theoretic
one would not.

## Scope

⚠️ **This unblocks nothing.**  It removes a false claim about what is reachable; the frontier of
`#244` is exactly where it was — `hprin` over a general field (`#962`) and the projective divisor
theory (`#639`).  ⚠️ `#251` used to be listed first and is **closed**
(`hasXCoordFormula_of_two_ne_zero`, `EllipticCurves.Torsion.NsmulOrder`; `y`-half
`nsmul_eq_some_omegaY_of_ΨSq_ne_zero`, `EllipticCurves.Torsion.NsmulYPeriodic`, `#1500`); removing
it from the list is not a claim that the frontier has moved.  ⚠️ **The clause this paragraph used to
end with has been paid** — it read *"A general-`n` statement would need `mulByNEndo`, which does not
exist"*.  `mulByNEndo` is `EllipticCurves.FunctionField.MulByNPullback`'s, at every `n`, and it was
never what a general-`n` version of *this* statement needed: the subject here is the bundled
`weilPairingTorsionMuHom_two` / `weilPairingTorsionMuHom_three`, and the counting inputs the
argument runs on are `card_torsion_two` / `card_torsion_three`.  Both are `n`-indexed for reasons
that have nothing to do with `[n]∗`.

⚠️ **`#404` is closed — and so is the statement the general-`n` entry above was relettered to.**
PR #557 proved the on-curve identity for `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` at every index over every commutative
ring — `WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero`, `EllipticCurves.Torsion.OmegaCrux`.
The *other* statement this tree also called `ωₙ` — the identification of those coordinates with the
**group-law** multiple `n • P` — is `#251` on its `x`-half and `#1500` on its `y`-half, and **both
are closed**: `hasXCoordFormula_of_two_ne_zero` (`EllipticCurves.Torsion.NsmulOrder`) and
`nsmul_eq_some_omegaY_of_ΨSq_ne_zero` (`EllipticCurves.Torsion.NsmulYPeriodic`, PR #579), each at
every index over a field with `(2 : F) ≠ 0` and under the same `ΨSqₙ(x) ≠ 0`.  ⚠️ **So the entry is
retired, not relettered a second time**: the coordinate formula gates nothing here.  ⚠️ What *does*
stand between this file and a general index was **not** re-measured when the entry was retired — do
not read this paragraph as putting `#1184`, `#938` or `#962` in its place.  The two-reading account
is `EllipticCurves.FunctionField.MulByNPullback`.

Everything below carries `[IsAlgClosed F]`, and it is load-bearing twice over: both cardinalities
are theorems about an algebraically closed field.  Over a general field `#E[n]` can be smaller than
`n²` and `#μ_n(F)` smaller than `n`, so the counting argument says nothing.

⚠️ **And over a general field the conclusion is not merely unproved — it can be false.**  The
statements below fix no `S` and impose no `S ≠ O`; `hu` is satisfied over *any* field by
`f = gS = 1`, `u = 1` (both sides are `1`, since `mulByTwoEndo` is a ring hom).  So on a curve
whose rational `n`-torsion is trivial — `y² = x³ + x + 1` over `ℚ` at `n = 2`, where the cubic has
no rational root, so `E[2](ℚ) = {O}` — the domain `Multiplicative (W.torsion 2)` is a subsingleton
and the map *is* injective.  What survives over a general field is the group-theoretic statement
for an `F`-rational `S` of order `n` that the `## The proof, and the standard reason it does not
use` section gives, and that is not formalised.

## ⚠️ Two `#903` citations in this file meant `#893`

Corrected in place, not retired.  `WeilPairingTranslationSlotNondegenerate`'s creation commit reads
`… (#893) (#357)`, so the module citation at the head of this file and the list of curve sources
in the non-vacuity section both wanted **`#893`**.  `#903` is the *"only `#print axioms` on the
fully qualified name checks placement"* protocol issue, whose PR is a namespace and suffix
refactor of `WeilPairingAlternatingBaseChange` and which certifies no curve — a digit
transposition that lands on a real issue, which is the more dangerous kind than one that lands on
nothing.

⚠️ This file was created on 2026-08-25, so the class is not historical residue that a one-time
sweep drains: the tree was still generating it on the day it was first swept.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1 — non-degeneracy is
  III.8.1(c), the alternating identity `e_n(S, S) = 1` is III.8.1(b).
-/

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] [IsAlgClosed F] {W : Affine F} [W.IsElliptic]

/-! ### `n = 2` -/

open Classical in
/-- **`e_2(S, ·) : E[2] → μ_2(F̄)` is not injective** over a field with `(2 : F) ≠ 0`, for every
`S`, every rung-5 root `gS` and every certificate `hu`.

⚠️ Not a gap in the pairing and not a statement that could be improved: `#E[2] = 4`
(`card_torsion_two`) and `#μ_2(F̄) = 2` (`natCard_rootsOfUnity_of_ne_zero`), so no injection
exists.  What non-degeneracy asserts about this map is `≠ 1`
(`weilPairingTorsionMuHom_two_ne_one`), and what is injective is the *other* slot,
`S ↦ e_2(S, ·)` into the dual group (`bijective_weilPairingTwoHom`). -/
theorem not_injective_weilPairingTorsionMuHom_two (h2 : (2 : F) ≠ 0) {f gS : W.FunctionField}
    {u : W.CoordinateRingˣ} (hgS : gS ≠ 0)
    (hu : (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f) :
    ¬ Function.Injective (weilPairingTorsionMuHom_two h2 hgS hu) := fun hinj => by
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_congr Multiplicative.toAdd, card_torsion_two h2,
    natCard_rootsOfUnity_of_ne_zero (F := F) (n := 2) h2] at hle
  omega

open Classical in
/-- **The kernel of `e_2(S, ·)` is not trivial.**  The `MonoidHom.ker` form of
`not_injective_weilPairingTorsionMuHom_two`, and the companion of
`ker_weilPairingTorsionMuHom_two_ne_top`
(`EllipticCurves.FunctionField.WeilPairingTranslationSlotNondegenerate`): the kernel is a proper
subgroup of `E[2]` and it is not the trivial one. -/
theorem ker_weilPairingTorsionMuHom_two_ne_bot (h2 : (2 : F) ≠ 0) {f gS : W.FunctionField}
    {u : W.CoordinateRingˣ} (hgS : gS ≠ 0)
    (hu : (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f) :
    MonoidHom.ker (weilPairingTorsionMuHom_two h2 hgS hu) ≠ ⊥ := fun hbot =>
  not_injective_weilPairingTorsionMuHom_two h2 hgS hu (MonoidHom.ker_eq_bot_iff _ |>.mp hbot)

/-! ### `n = 3` -/

open Classical in
/-- **`e_3(S, ·) : E[3] → μ_3(F̄)` is not injective.**  The mirror of
`not_injective_weilPairingTorsionMuHom_two`, off `card_torsion_three` (`#E[3] = 9`) against
`#μ_3(F̄) = 3`.

⚠️ It is a transcription and not a re-derivation: `card_torsion_three` needs **both** `(2 : F) ≠ 0`
and `(3 : F) ≠ 0`, and `weilPairingTorsionMuHom_three` already carries both, so no hypothesis is
added.  `natCard_rootsOfUnity_of_ne_zero` is fed `h3` here where the `n = 2` statement feeds it
`h2`. -/
theorem not_injective_weilPairingTorsionMuHom_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {f gS : W.FunctionField} {u : W.CoordinateRingˣ} (hgS : gS ≠ 0)
    (hu : (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f) :
    ¬ Function.Injective (weilPairingTorsionMuHom_three h2 h3 hgS hu) := fun hinj => by
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_congr Multiplicative.toAdd, card_torsion_three h2 h3,
    natCard_rootsOfUnity_of_ne_zero (F := F) (n := 3) h3] at hle
  omega

open Classical in
/-- **The kernel of `e_3(S, ·)` is not trivial.**  The `n = 3` mirror of
`ker_weilPairingTorsionMuHom_two_ne_bot`. -/
theorem ker_weilPairingTorsionMuHom_three_ne_bot (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {f gS : W.FunctionField} {u : W.CoordinateRingˣ} (hgS : gS ≠ 0)
    (hu : (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f) :
    MonoidHom.ker (weilPairingTorsionMuHom_three h2 h3 hgS hu) ≠ ⊥ := fun hbot =>
  not_injective_weilPairingTorsionMuHom_three h2 h3 hgS hu
    (MonoidHom.ker_eq_bot_iff _ |>.mp hbot)

end CoordinateRing

/-! ### Non-vacuity

A negative headline needs a witness that its hypotheses are satisfiable, or it is a statement about
the empty set.  The curves are the ones `#845`/`#861`/`#873`/`#890`/`#893` use — `y² = x³ − x` with
`S = (0, 0) ∈ E[2]` and `y² + y = x³` with `S = (0, 0) ∈ E[3]`, both over `AlgebraicClosure ℚ` —
and the rung-5 root and its certificate are produced by `exists_gS_two_of_isAlgClosed` and
`exists_gS_three_of_isAlgClosed`, so nothing is assumed.

⚠️ Each certificate below therefore says something stronger than the theorem it instantiates: on a
named curve, at a named point, a genuine `e_n(S, ·)` exists **and** is not injective. -/

section Nonvacuity

open CoordinateRing

/-! The certificate curves `y² = x³ − x` and `y² + y = x³` are the shared
`EllipticCurves.Fixture.y2EqX3SubX` and `EllipticCurves.Fixture.y2AddYEqX3`, and the base —
algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here. -/

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

private lemma exampleNsS : (y2EqX3SubX AlgClosedQ).Nonsingular 0 0 :=
  (y2EqX3SubX AlgClosedQ).equation_iff_nonsingular.mp (by
    norm_num [y2EqX3SubX, WeierstrassCurve.Affine.equation_iff])

open Classical in
private lemma exampleTorS :
    Point.some (0 : AlgClosedQ) 0 exampleNsS ∈ (y2EqX3SubX AlgClosedQ).torsion 2 :=
  (mem_torsion_two_some_iff exampleNsS).mpr (by norm_num [y2EqX3SubX])

open Classical in
/-- **A genuine `e_2(S, ·)` on a curve that exists, and it is not injective.**
`S = (0, 0)` on `y² = x³ − x`; no hypothesis survives. -/
example : ∃ (gS : (y2EqX3SubX AlgClosedQ).FunctionField) (hgS : gS ≠ 0) (f :
    (y2EqX3SubX AlgClosedQ).FunctionField)
    (u : (y2EqX3SubX AlgClosedQ).CoordinateRingˣ)
    (hu : (u : (y2EqX3SubX AlgClosedQ).CoordinateRing) • gS ^ 2 = mulByTwoEndo exampleTwo f),
    ¬ Function.Injective (weilPairingTorsionMuHom_two exampleTwo hgS hu) := by
  obtain ⟨f, -, -, gS, hgS, u, hu⟩ := exists_gS_two_of_isAlgClosed exampleTwo exampleNsS exampleTorS
  exact ⟨gS, hgS, f, u, hu, not_injective_weilPairingTorsionMuHom_two exampleTwo hgS hu⟩

private lemma exampleNsThreeS : (y2AddYEqX3 AlgClosedQ).Nonsingular 0 0 :=
  (y2AddYEqX3 AlgClosedQ).equation_iff_nonsingular.mp (by
    norm_num [y2AddYEqX3, WeierstrassCurve.Affine.equation_iff])

open Classical in
private lemma exampleTorThreeS :
    Point.some (0 : AlgClosedQ) 0 exampleNsThreeS ∈ (y2AddYEqX3 AlgClosedQ).torsion 3 :=
  mem_torsion_three_some_iff'.mpr (by
    norm_num [y2AddYEqX3, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈])

open Classical in
/-- **A genuine `e_3(S, ·)` on a curve that exists, and it is not injective.**
`S = (0, 0)` on `y² + y = x³`. -/
example : ∃ (gS : (y2AddYEqX3 AlgClosedQ).FunctionField) (hgS : gS ≠ 0)
    (f : (y2AddYEqX3 AlgClosedQ).FunctionField) (u : (y2AddYEqX3 AlgClosedQ).CoordinateRingˣ)
    (hu : (u : (y2AddYEqX3 AlgClosedQ).CoordinateRing) • gS ^ 3
      = mulByThreeEndo exampleTwo exampleThree f),
    ¬ Function.Injective (weilPairingTorsionMuHom_three exampleTwo exampleThree hgS hu) := by
  obtain ⟨f, -, -, gS, hgS, u, hu⟩ :=
    exists_gS_three_of_isAlgClosed exampleTwo exampleThree exampleNsThreeS exampleTorThreeS
  exact ⟨gS, hgS, f, u, hu,
    not_injective_weilPairingTorsionMuHom_three exampleTwo exampleThree hgS hu⟩

end Nonvacuity

end WeierstrassCurve.Affine
