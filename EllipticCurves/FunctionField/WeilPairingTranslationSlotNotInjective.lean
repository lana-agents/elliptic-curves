/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairingSurjective
import EllipticCurves.FunctionField.WeilPairingTranslationSlotNondegenerate

/-!
# `e_n(S, ·) : E[n] → μ_n(F̄)` is **never** injective, at `n = 2` and `n = 3`

`EllipticCurves.FunctionField.WeilPairingTranslationSlotNondegenerate` (`#903`) proves that the
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
  `…_three` — the map is not injective, for **every** `S`, every rung-5 root and every certificate;
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
here: `e_n(S, S) = 1`, so `⟨S⟩` lies in the kernel and injectivity fails for every `n ≥ 2` over
**any** base field, closed or not.  This tree does prove that alternating identity, but only in an
`∃`-shape that produces its own root and certificate
(`exists_weilPairingMu_self_eq_one_of_isAlgClosed_two`,
`EllipticCurves.FunctionField.WeilPairingAlternatingTwoAlgClosed`), so it cannot be applied to the
arbitrary `hgS`/`hu` the statements below quantify over.  **Saying which argument is used and which
is merely true is the point**: the counting proof needs `[IsAlgClosed F]` and the group-theoretic
one would not.

## Scope

⚠️ **This unblocks nothing.**  It removes a false claim about what is reachable; the frontier of
`#244` is exactly where it was — `#404`'s `ωₙ` for general `n`, `hprin` over a general field
(`#962`), the projective divisor theory (`#639`).  A general-`n` statement would need
`mulByNEndo`, which does not exist.

Everything below carries `[IsAlgClosed F]`, and it is load-bearing twice over: both cardinalities
are theorems about an algebraically closed field.  Over a general field `#E[n]` can be smaller than
`n²` and `#μ_n(F)` smaller than `n`, so the counting argument says nothing — the statement is still
false there, but for the group-theoretic reason the `## The proof, and the standard reason it does
not use` section gives, which is not formalised.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1 — non-degeneracy is
  III.8.1(d), the alternating identity `e_n(S, S) = 1` is III.8.1(b).
-/

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] [IsAlgClosed F] {W : Affine F} [W.IsElliptic]

/-! ### `n = 2` -/

open Classical in
/-- **`e_2(S, ·) : E[2] → μ_2(F̄)` is not injective**, for every `S`, every rung-5 root `gS` and
every certificate `hu`.

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
the empty set.  The curves are the ones `#845`/`#861`/`#873`/`#890`/`#903` use — `y² = x³ − x` with
`S = (0, 0) ∈ E[2]` and `y² + y = x³` with `S = (0, 0) ∈ E[3]`, both over `AlgebraicClosure ℚ` —
and the rung-5 root and its certificate are produced by `exists_gS_two_of_isAlgClosed` and
`exists_gS_three_of_isAlgClosed`, so nothing is assumed.

⚠️ Each certificate below therefore says something stronger than the theorem it instantiates: on a
named curve, at a named point, a genuine `e_n(S, ·)` exists **and** is not injective. -/

section Nonvacuity

open CoordinateRing

/-- An algebraically closed field of characteristic zero. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

private lemma exampleTwo : (2 : exampleField) ≠ 0 := by norm_num

private lemma exampleThree : (3 : exampleField) ≠ 0 := by norm_num

/-- The curve `y² = x³ − x` over `AlgebraicClosure ℚ`, of discriminant `64`. -/
private noncomputable def exampleCurve : Affine exampleField := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleNsS : exampleCurve.Nonsingular 0 0 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

open Classical in
private lemma exampleTorS :
    Point.some (0 : exampleField) 0 exampleNsS ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNsS).mpr (by norm_num [exampleCurve])

open Classical in
/-- **A genuine `e_2(S, ·)` on a curve that exists, and it is not injective.**
`S = (0, 0)` on `y² = x³ − x`; no hypothesis survives. -/
example : ∃ (gS : exampleCurve.FunctionField) (hgS : gS ≠ 0) (f : exampleCurve.FunctionField)
    (u : exampleCurve.CoordinateRingˣ)
    (hu : (u : exampleCurve.CoordinateRing) • gS ^ 2 = mulByTwoEndo exampleTwo f),
    ¬ Function.Injective (weilPairingTorsionMuHom_two exampleTwo hgS hu) := by
  obtain ⟨f, -, -, gS, hgS, u, hu⟩ := exists_gS_two_of_isAlgClosed exampleTwo exampleNsS exampleTorS
  exact ⟨gS, hgS, f, u, hu, not_injective_weilPairingTorsionMuHom_two exampleTwo hgS hu⟩

/-- The curve `y² + y = x³` over `AlgebraicClosure ℚ`, of discriminant `−27`. -/
private noncomputable def exampleCurveThree : Affine exampleField := ⟨0, 0, 1, 0, 0⟩

private instance : exampleCurveThree.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurveThree, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleNsThreeS : exampleCurveThree.Nonsingular 0 0 :=
  exampleCurveThree.equation_iff_nonsingular.mp (by
    norm_num [exampleCurveThree, WeierstrassCurve.Affine.equation_iff])

open Classical in
private lemma exampleTorThreeS :
    Point.some (0 : exampleField) 0 exampleNsThreeS ∈ exampleCurveThree.torsion 3 :=
  mem_torsion_three_some_iff'.mpr (by
    norm_num [exampleCurveThree, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈])

open Classical in
/-- **A genuine `e_3(S, ·)` on a curve that exists, and it is not injective.**
`S = (0, 0)` on `y² + y = x³`. -/
example : ∃ (gS : exampleCurveThree.FunctionField) (hgS : gS ≠ 0)
    (f : exampleCurveThree.FunctionField) (u : exampleCurveThree.CoordinateRingˣ)
    (hu : (u : exampleCurveThree.CoordinateRing) • gS ^ 3
      = mulByThreeEndo exampleTwo exampleThree f),
    ¬ Function.Injective (weilPairingTorsionMuHom_three exampleTwo exampleThree hgS hu) := by
  obtain ⟨f, -, -, gS, hgS, u, hu⟩ :=
    exists_gS_three_of_isAlgClosed exampleTwo exampleThree exampleNsThreeS exampleTorThreeS
  exact ⟨gS, hgS, f, u, hu,
    not_injective_weilPairingTorsionMuHom_three exampleTwo exampleThree hgS hu⟩

end Nonvacuity

end WeierstrassCurve.Affine
