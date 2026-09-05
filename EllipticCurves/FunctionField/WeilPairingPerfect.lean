/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.GroupTheory.FiniteAbelian.Duality
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.WeilPairingSurjective
import EllipticCurves.Torsion.ThreeTorsionStructure

/-!
# The Weil pairing is perfect: `E[n]` is its own dual at `n = 2` and `n = 3`

`EllipticCurves.FunctionField.WeilPairingFunctionTwo` (`#922`) and
`EllipticCurves.FunctionField.WeilPairingFunctionThree` (`#925`) bundled the pairing as

```
weilPairing{Two,Three}Hom : Multiplicative E[n] →* (Multiplicative E[n] →* μ_n(F̄))
```

and proved `MonoidHom.ker _ = ⊥`, i.e. that `S ↦ e_n(S, ·)` is **injective** into the dual group.
`EllipticCurves.FunctionField.WeilPairingSurjective` (`#938`) then showed each individual slot map
is onto `μ_n(F̄)`.  Neither says that *every* character of `E[n]` arises as `e_n(S, ·)`.  This file
does: the bundled map is **bijective**, so

```
E[n] ≅ E[n]^∨ = (Multiplicative E[n] →* μ_n(F̄))     as groups,
```

which is what "the Weil pairing is a perfect pairing" means.

## The argument, and the two places `#938`'s recorded route was wrong

`#938`'s out-of-scope section sketched this and warned the route was not spiked.  Spiking it
corrected it twice, so the corrections are recorded here rather than left as folklore.

`Mathlib.GroupTheory.FiniteAbelian.Duality` gives `Nat.card (G →* Mˣ) = Nat.card G` for a finite
abelian `G` and a monoid `M` with enough `n`-th roots of unity, `n` the exponent of `G`.  Our
bundled map is injective, and its source and target both have `Nat.card = Nat.card E[n]`, so it is
bijective.  Two steps carry all the content:

* ⚠️ **The exponent never has to be computed.**  `HasEnoughRootsOfUnity.of_dvd` converts
  `Monoid.exponent G ∣ n` into the instance the duality theorem wants, and `∀ g, g ^ n = 1` gives
  that divisibility.  So `pow_eq_one_multiplicative_torsion` — two lines, general in `n`, needing
  neither an algebraic closure nor `[W.IsElliptic]` — replaces the equality
  `Monoid.exponent (Multiplicative E[2]) = 2`, which would additionally have had to rule out `E[2]`
  being trivial.
* ⚠️ **The `rootsOfUnity`-versus-`Fˣ` bridge is `MonoidHom.codRestrict`, not
  `rootsOfUnityUnitsMulEquiv`.**  A homomorphism out of a group killed by `n` lands in
  `rootsOfUnity n F` whether or not it was told to, so composing with `Subgroup.subtype` one way and
  `codRestrict` the other is a bijection with both round-trips `rfl`
  (`monoidHomRootsOfUnityEquiv`).

⚠️ **`card_torsion_two` is not needed for the perfect-pairing theorem.**  The duality count is
`Nat.card (G →* μ_n) = Nat.card G` for the *same* `G` on both sides, so "injective between finite
sets of equal size" closes without the number ever being named.  `card_torsion_two` and
`card_torsion_three` enter only in `natCard_monoidHom_torsion{Two,Three}`, which is where the
numbers `4` and `9` are actually claimed.

## Main statements

* `monoidHomRootsOfUnityEquiv` — homomorphisms into `rootsOfUnity n F` are homomorphisms into `Fˣ`,
  for a source killed by `n`; a statement about groups and a field, in the root namespace.
* `natCard_monoidHom_rootsOfUnity` — `#(G →* μ_n(F̄)) = #G`; likewise root-namespace.
* `WeierstrassCurve.Affine.pow_eq_one_multiplicative_torsion` — `E[n]`, written multiplicatively, is
  killed by `n`.  General in `n`, and over an arbitrary field.
* `WeierstrassCurve.Affine.bijective_weilPairingTwoHom`, `…bijective_weilPairingThreeHom` — **the
  perfect-pairing statement**.
* `WeierstrassCurve.Affine.weilPairingTwoEquiv`, `…weilPairingThreeEquiv` — the same bundled as a
  `MulEquiv` onto the dual group.
* `WeierstrassCurve.Affine.existsUnique_weilPairingTwoHom_eq`, `…Three…` — the reading a consumer
  quotes: every character of `E[n]` is `e_n(S, ·)` for exactly one `S`.
* `WeierstrassCurve.Affine.natCard_monoidHom_torsionTwo`, `…Three` — `#E[2]^∨ = 4`, `#E[3]^∨ = 9`.

## Naming and placement

The two curve-free inputs sit at the root, above `namespace WeierstrassCurve.Affine`, and belong
upstream in Mathlib; `#938` placed `natCard_rootsOfUnity_of_ne_zero` the same way and for the same
reason.  Putting a curve namespace on a curve-free statement is `#903`'s defect one level up.
Everything else is in `WeierstrassCurve.Affine` with `open CoordinateRing`, `#903`'s house pattern
as enforced by `#918` and `#927`.

## Explicitly out of scope

* **General `n`** — out of scope here.  ⚠️ This bullet used to blame `#251`, and before that
  `#404`; both are closed, and it is **not** Ward-blocked either: see below.
  ⚠️ **But the second obstruction `#938` carries does not apply here, and a reader will assume it
  does.**  `#938`'s surjectivity argument runs through a group of *prime* order and has no analogue
  at composite `n`; Mathlib's duality is stated for an arbitrary finite abelian group, so the
  argument in this file would transcribe unchanged to any `n` for which `weilPairingNHom` and
  `ker_weilPairingNHom` existed.  One obstruction here, two there.
* **`E[n] ≅ (ℤ/nℤ)²`** — `#242`/`#293`, a different statement whose `n = 2` and `n = 3` instances
  are already merged (`nonempty_torsionTwo_addEquiv`, `nonempty_torsionThree_addEquiv`).  ⚠️ This
  file deliberately does **not** route through them: the duality count needs only finiteness, and
  going via the structure theorem would make this module depend on strictly more for nothing.
* **The double dual.**  `CommGroup.monoidHomMonoidHomEquiv` sits in the same Mathlib file and would
  compose with `weilPairingTwoEquiv` in one line; there is no consumer, so it is absent on purpose.
* **The arbitrary-field (`_of_hprin`) form.**  Inherited from `#938` and false rather than weaker:
  the duality instance is `HasEnoughRootsOfUnity F n`, which is exactly the second, independent job
  `[IsAlgClosed F]` does on this front.  Over a non-closed `F` the dual group is smaller than
  `E[n]` and the map is not onto.  There is nothing to lift.
* **Galois-equivariance of the equiv.**  `#936` left bundled-hom equivariance unfiled for want of a
  consumer and that reasoning is unchanged here.

⚠️ **`#404` is closed — and so is the statement the general-`n` entry above was relettered to.**
PR #557 proved the on-curve identity for `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` at every index over a field with
`(2 : F) ≠ 0` and under `ψₙ(x, y) ≠ 0` — `WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero`,
`EllipticCurves.Torsion.OmegaCrux`.  The *other* statement this tree also called `ωₙ` — the
identification of those coordinates with the **group-law** multiple `n • P` — is `#251` on its
`x`-half and `#1500` on its `y`-half, and **both are closed**: `hasXCoordFormula_of_two_ne_zero`
(`EllipticCurves.Torsion.NsmulOrder`) and `nsmul_eq_some_omegaY_of_ΨSq_ne_zero`
(`EllipticCurves.Torsion.NsmulYPeriodic`, PR #579), each at every index over a field with
`(2 : F) ≠ 0` and under the same `ΨSqₙ(x) ≠ 0`.  ⚠️ **So the entry is retired, not relettered a
second time**: the coordinate formula gates nothing here.  ⚠️ What *does* stand between this file
and a general index was **not** re-measured when the entry was retired — do not read this paragraph
as putting `#1184`, `#938` or `#962` in its place.  The two-reading account is
`EllipticCurves.FunctionField.MulByNPullback`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8, Prop. 8.1(c).
-/

/-- **Homomorphisms into `μ_n(F)` are homomorphisms into `Fˣ`**, when the source is killed by `n`.

The forward map composes with `Subgroup.subtype` and the inverse is `MonoidHom.codRestrict`: a
homomorphism `ψ : G →* Fˣ` out of a group with `g ^ n = 1` satisfies `(ψ g) ^ n = 1`, so it lands
in `rootsOfUnity n F` whether or not it was told to.  Both round-trips are `rfl`.

A statement about a group and a field and nothing else; it belongs in Mathlib.

⚠️ Not `noncomputable`: every field is `MonoidHom.comp`, `Subgroup.subtype` or
`MonoidHom.codRestrict`, and nothing here chooses.  `#print axioms` agrees — this is the one
declaration in the file that does not depend on `Classical.choice`. -/
def monoidHomRootsOfUnityEquiv {F : Type*} [Field F] {G : Type*} [CommGroup G]
    {n : ℕ} (hG : ∀ g : G, g ^ n = 1) : (G →* (rootsOfUnity n F)) ≃ (G →* Fˣ) where
  toFun φ := (rootsOfUnity n F).subtype.comp φ
  invFun ψ := ψ.codRestrict (rootsOfUnity n F) (fun g => by
    rw [mem_rootsOfUnity, ← map_pow, hG g, map_one])
  left_inv φ := by ext g; rfl
  right_inv ψ := by ext g; rfl

/-- **The dual of a finite abelian group killed by `n` has the same order as the group**, over an
algebraically closed field in which `n` is invertible.

⚠️ The exponent of `G` is never computed: `HasEnoughRootsOfUnity.of_dvd` only needs
`Monoid.exponent G ∣ n`, which `hG` supplies.  That is what keeps the curve-side hypothesis down to
`∀ g, g ^ n = 1`.

A statement about a group and a field and nothing else; it belongs in Mathlib beside
`CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity`, which is most of its proof. -/
theorem natCard_monoidHom_rootsOfUnity {F : Type*} [Field F] [IsAlgClosed F] {G : Type*}
    [CommGroup G] [Finite G] {n : ℕ} (hn : (n : F) ≠ 0) (hG : ∀ g : G, g ^ n = 1) :
    Nat.card (G →* (rootsOfUnity n F)) = Nat.card G := by
  haveI : NeZero n := ⟨fun h => hn (by simp [h])⟩
  haveI : NeZero ((n : ℕ) : F) := ⟨hn⟩
  haveI : HasEnoughRootsOfUnity F n := IsSepClosed.hasEnoughRootsOfUnity F n
  haveI : HasEnoughRootsOfUnity F (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd F (Monoid.exponent_dvd_of_forall_pow_eq_one hG)
  rw [Nat.card_congr (monoidHomRootsOfUnityEquiv (F := F) hG),
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G F]

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

open Classical in
/-- **`E[n]` written multiplicatively is killed by `n`.**  This is the whole curve-side input to the
duality count, and it is general in `n`, over an arbitrary field, with no elliptic hypothesis.

⚠️ Stated before `[IsAlgClosed F]` and `[W.IsElliptic]` enter scope, because it needs neither and
the `unusedSectionVars` linter would otherwise fire. -/
theorem pow_eq_one_multiplicative_torsion {n : ℕ} (g : Multiplicative (W.torsion n)) : g ^ n = 1 :=
  Multiplicative.toAdd.injective (by simp)

variable [IsAlgClosed F] [W.IsElliptic]

/-! ### `n = 2` -/

open Classical in
/-- **The Weil pairing at `n = 2` is perfect**: `S ↦ e_2(S, ·)` is a bijection from `E[2]` onto its
dual group `Multiplicative E[2] →* μ_2(F̄)`.

Injectivity is `ker_weilPairingTwoHom` (`#922`).  The two sides have the same finite cardinality by
`natCard_monoidHom_rootsOfUnity`, which is where Mathlib's finite-abelian duality enters.  ⚠️ The
number `4` is not used: the count is `#(G →* μ_2) = #G` for the same `G` on both sides. -/
theorem bijective_weilPairingTwoHom (h2 : (2 : F) ≠ 0) :
    Function.Bijective (weilPairingTwoHom (W := W) h2) := by
  haveI := W.finite_torsion_two h2
  haveI : Finite (Multiplicative (W.torsion 2)) := inferInstanceAs (Finite (W.torsion 2))
  have hcard : Nat.card (Multiplicative (W.torsion 2) →* rootsOfUnity 2 F)
      = Nat.card (Multiplicative (W.torsion 2)) :=
    natCard_monoidHom_rootsOfUnity h2 pow_eq_one_multiplicative_torsion
  haveI : Finite (Multiplicative (W.torsion 2) →* rootsOfUnity 2 F) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  exact (Nat.bijective_iff_injective_and_card _).mpr
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (ker_weilPairingTwoHom h2), hcard.symm⟩

open Classical in
/-- **`E[2] ≅ E[2]^∨`**, the perfect pairing bundled as a group isomorphism onto the dual. -/
noncomputable def weilPairingTwoEquiv (h2 : (2 : F) ≠ 0) :
    Multiplicative (W.torsion 2) ≃* (Multiplicative (W.torsion 2) →* rootsOfUnity 2 F) :=
  MulEquiv.ofBijective _ (bijective_weilPairingTwoHom h2)

open Classical in
/-- **Every character of `E[2]` is `e_2(S, ·)` for exactly one `S`** — the reading of perfectness a
consumer quotes, with no `MulEquiv` to unfold. -/
theorem existsUnique_weilPairingTwoHom_eq (h2 : (2 : F) ≠ 0)
    (φ : Multiplicative (W.torsion 2) →* rootsOfUnity 2 F) :
    ∃! S : Multiplicative (W.torsion 2), weilPairingTwoHom h2 S = φ :=
  (bijective_weilPairingTwoHom h2).existsUnique φ

open Classical in
/-- **`#E[2]^∨ = 4`.**  ⚠️ This is the one statement in the file that consumes `card_torsion_two`;
the perfect-pairing theorem above does not. -/
theorem natCard_monoidHom_torsionTwo (h2 : (2 : F) ≠ 0) :
    Nat.card (Multiplicative (W.torsion 2) →* rootsOfUnity 2 F) = 4 := by
  haveI := W.finite_torsion_two h2
  haveI : Finite (Multiplicative (W.torsion 2)) := inferInstanceAs (Finite (W.torsion 2))
  rw [natCard_monoidHom_rootsOfUnity h2 pow_eq_one_multiplicative_torsion,
    Nat.card_congr Multiplicative.toAdd, card_torsion_two h2]

/-! ### `n = 3` -/

open Classical in
/-- **The Weil pairing at `n = 3` is perfect**, the mirror of `bijective_weilPairingTwoHom`.

⚠️ Note which hypothesis does what: finiteness of `E[3]` and the order of `μ_3(F̄)` are gated on
`h3` alone, and `h2` enters only through `ker_weilPairingThreeHom`.  Both are genuine. -/
theorem bijective_weilPairingThreeHom (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Function.Bijective (weilPairingThreeHom (W := W) h2 h3) := by
  haveI := W.finite_torsion_three h3
  haveI : Finite (Multiplicative (W.torsion 3)) := inferInstanceAs (Finite (W.torsion 3))
  have hcard : Nat.card (Multiplicative (W.torsion 3) →* rootsOfUnity 3 F)
      = Nat.card (Multiplicative (W.torsion 3)) :=
    natCard_monoidHom_rootsOfUnity h3 pow_eq_one_multiplicative_torsion
  haveI : Finite (Multiplicative (W.torsion 3) →* rootsOfUnity 3 F) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  exact (Nat.bijective_iff_injective_and_card _).mpr
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (ker_weilPairingThreeHom h2 h3), hcard.symm⟩

open Classical in
/-- **`E[3] ≅ E[3]^∨`**, the perfect pairing bundled as a group isomorphism onto the dual. -/
noncomputable def weilPairingThreeEquiv (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Multiplicative (W.torsion 3) ≃* (Multiplicative (W.torsion 3) →* rootsOfUnity 3 F) :=
  MulEquiv.ofBijective _ (bijective_weilPairingThreeHom h2 h3)

open Classical in
/-- **Every character of `E[3]` is `e_3(S, ·)` for exactly one `S`.** -/
theorem existsUnique_weilPairingThreeHom_eq (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (φ : Multiplicative (W.torsion 3) →* rootsOfUnity 3 F) :
    ∃! S : Multiplicative (W.torsion 3), weilPairingThreeHom h2 h3 S = φ :=
  (bijective_weilPairingThreeHom h2 h3).existsUnique φ

open Classical in
/-- **`#E[3]^∨ = 9`**, the one statement at `n = 3` that consumes `card_torsion_three`. -/
theorem natCard_monoidHom_torsionThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nat.card (Multiplicative (W.torsion 3) →* rootsOfUnity 3 F) = 9 := by
  haveI := W.finite_torsion_three h3
  haveI : Finite (Multiplicative (W.torsion 3)) := inferInstanceAs (Finite (W.torsion 3))
  rw [natCard_monoidHom_rootsOfUnity h3 pow_eq_one_multiplicative_torsion,
    Nat.card_congr Multiplicative.toAdd, card_torsion_three h2 h3]

/-! ### Non-vacuity

Everything above carries `[IsAlgClosed F]` and `[W.IsElliptic]`, so `ℚ` cannot witness it.  The
curves are `WeilPairingSurjective`'s own — `y² = x³ − x` at `n = 2` and `y² + y = x³` at `n = 3`,
both over `AlgebraicClosure ℚ`.

⚠️ **Which certificates are load-bearing.**  A bare named-curve instance of a bijectivity claim is
weightless in `#916`'s sense — it says the construction elaborates on a curve that exists.  Two of
this block's certificates carry real weight, by two different tests.

⚠️ **The refutations, `#925`'s test.**  `#925`'s technique is to substitute a degenerate argument
and compile the refutation, and it **does** apply here — the degenerate substitution is in the
**map** slot, not in a point slot.  `not_bijective_one_two` and `not_bijective_one_three` below
compile the statement that the *trivial* bilinear map on the very same curve is **not** bijective,
so the perfectness theorems are facts about this pairing and not about the shape of the sentence.
⚠️ Each refutation consumes `card_torsion_two` or `card_torsion_three` — the same independent input
the numeric certificate below consumes — so the pair certifies that input in both directions.

> **The generalisation, which is the reusable part**: when a statement has no argument to
> degenerate, look for a *degenerate inhabitant of the object it is about*.  "Is this map
> bijective" has no point slot, but it does have a map slot, and `1` lives in it.

⚠️ **The numeric ones.**  `Nat.card (Multiplicative E[2] →* μ_2) = 4` and its `n = 3` analogue are
false at every other value, they consume `card_torsion_two` / `card_torsion_three` on top of the
duality count, and `:= rfl` does not prove them (checked: it reports
`Type mismatch: rfl has type ?m = ?m`, `Nat.card … = 4` being no reducible identity). -/

section Nonvacuity

/-! The certificate curves `y² = x³ − x` and `y² + y = x³` are the shared
`EllipticCurves.Fixture.y2EqX3SubX` and `EllipticCurves.Fixture.y2AddYEqX3`, and the base —
algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here. -/

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

open Classical in
/-- The pairing on `y² = x³ − x` identifies `E[2]` with its dual — the weightless certificate, and
this block says so rather than presenting it as more. -/
example : Function.Bijective (weilPairingTwoHom (W := y2EqX3SubX AlgClosedQ) exampleTwo) :=
  bijective_weilPairingTwoHom exampleTwo

open Classical in
/-- Every character of `E[2]` on that curve is `e_2(S, ·)` for exactly one `S`. -/
example (φ : Multiplicative ((y2EqX3SubX AlgClosedQ).torsion 2) →* rootsOfUnity 2 AlgClosedQ) :
    ∃! S : Multiplicative ((y2EqX3SubX AlgClosedQ).torsion 2),
      weilPairingTwoHom exampleTwo S = φ :=
  existsUnique_weilPairingTwoHom_eq exampleTwo φ

open Classical in
/-- **⚠️ The load-bearing certificate at `n = 2`**: the dual of `E[2]` on `y² = x³ − x` has exactly
four elements.  Named number, supplied by `card_torsion_two` on top of the duality count, and not
provable by `rfl`. -/
example :
    Nat.card (Multiplicative ((y2EqX3SubX AlgClosedQ).torsion 2) →* rootsOfUnity 2 AlgClosedQ)
        = 4 :=
  natCard_monoidHom_torsionTwo exampleTwo

open Classical in
/-- **⚠️ Why the bijectivity certificate above is not weightless**: the *same* claim about the
*trivial* bilinear map on the *same* curve is false, because `E[2]` has four elements and a constant
map is not injective.  This is a refutation checked by the build, not a failed proof attempt, and it
consumes `card_torsion_two` exactly as the numeric certificate does. -/
private theorem not_bijective_one_two :
    ¬ Function.Bijective
      (1 : Multiplicative ((y2EqX3SubX AlgClosedQ).torsion 2) →*
        Multiplicative ((y2EqX3SubX AlgClosedQ).torsion 2) →* rootsOfUnity 2 AlgClosedQ) := by
  intro hbij
  haveI := (y2EqX3SubX AlgClosedQ).finite_torsion_two exampleTwo
  have hcard : Nat.card (Multiplicative ((y2EqX3SubX AlgClosedQ).torsion 2)) = 4 := by
    rw [Nat.card_congr Multiplicative.toAdd, card_torsion_two exampleTwo]
  haveI hsub : Subsingleton (Multiplicative ((y2EqX3SubX AlgClosedQ).torsion 2)) :=
    ⟨fun a b => hbij.injective (by simp)⟩
  rw [Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩] at hcard
  exact absurd hcard (by norm_num)

open Classical in
/-- The pairing on `y² + y = x³` identifies `E[3]` with its dual. -/
example :
    Function.Bijective (weilPairingThreeHom (W := y2AddYEqX3 AlgClosedQ) exampleTwo exampleThree) :=
  bijective_weilPairingThreeHom exampleTwo exampleThree

open Classical in
/-- Every character of `E[3]` on that curve is `e_3(S, ·)` for exactly one `S`. -/
example (φ : Multiplicative ((y2AddYEqX3 AlgClosedQ).torsion 3) →* rootsOfUnity 3 AlgClosedQ) :
    ∃! S : Multiplicative ((y2AddYEqX3 AlgClosedQ).torsion 3),
      weilPairingThreeHom exampleTwo exampleThree S = φ :=
  existsUnique_weilPairingThreeHom_eq exampleTwo exampleThree φ

open Classical in
/-- **⚠️ The load-bearing certificate at `n = 3`**: the dual of `E[3]` on `y² + y = x³` has exactly
nine elements. -/
example :
    Nat.card (Multiplicative ((y2AddYEqX3 AlgClosedQ).torsion 3) →* rootsOfUnity 3 AlgClosedQ)
        = 9 :=
  natCard_monoidHom_torsionThree exampleTwo exampleThree

open Classical in
/-- **⚠️ Why the bijectivity certificate above is not weightless**, at `n = 3`: the trivial bilinear
map on the same curve is not bijective, `E[3]` having nine elements. -/
private theorem not_bijective_one_three :
    ¬ Function.Bijective
      (1 : Multiplicative ((y2AddYEqX3 AlgClosedQ).torsion 3) →*
        Multiplicative ((y2AddYEqX3 AlgClosedQ).torsion 3) →* rootsOfUnity 3 AlgClosedQ) := by
  intro hbij
  haveI := (y2AddYEqX3 AlgClosedQ).finite_torsion_three exampleThree
  have hcard : Nat.card (Multiplicative ((y2AddYEqX3 AlgClosedQ).torsion 3)) = 9 := by
    rw [Nat.card_congr Multiplicative.toAdd, card_torsion_three exampleTwo exampleThree]
  haveI hsub : Subsingleton (Multiplicative ((y2AddYEqX3 AlgClosedQ).torsion 3)) :=
    ⟨fun a b => hbij.injective (by simp)⟩
  rw [Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩] at hcard
  exact absurd hcard (by norm_num)

end Nonvacuity

end WeierstrassCurve.Affine
