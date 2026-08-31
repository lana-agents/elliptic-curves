/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import EllipticCurves.FunctionField.WeilPairingFunctionTwo
import EllipticCurves.FunctionField.WeilPairingFunctionThree

/-!
# The Weil pairing is onto `μ_n(F̄)`, and non-degenerate in the second slot too

`EllipticCurves.FunctionField.WeilPairingFunctionTwo` (`#922`) and
`EllipticCurves.FunctionField.WeilPairingFunctionThree` (`#925`) made the Weil pairing a function

```
weilPairingTwo   : E[2] → E[2] → μ_2(F̄),      weilPairingThree : E[3] → E[3] → μ_3(F̄)
```

and bundled each as `weilPairing{Two,Three}Hom`, a `MonoidHom` into a `MonoidHom`, with
`MonoidHom.ker _ = ⊥`.  That kernel statement says the **outer** slot is faithful: `S ↦ e_n(S, ·)`
is injective.  This file adds the two things a reader reaches for next and which no file in the
tree stated.

* **Surjectivity.** For `S ≠ 0` the map `T ↦ e_n(S, T)` is onto `μ_n(F̄)` — the pairing takes
  *every* `n`-th root of unity as a value, not merely some value `≠ 1`.
* **Non-degeneracy in the second slot.**  `eq_zero_of_forall_weilPairingTwo_eq_one` fixes `S` and
  quantifies `T`; the mirror fixes `T` and quantifies `S`, and bundled it is
  `MonoidHom.ker (weilPairingTwoHom h2).flip = ⊥`.

## Why surjectivity is not a corollary of the kernel statement

`ker _ = ⊥` gives, for `S ≠ 0`, only that the homomorphism `e_n(S, ·) : E[n] → μ_n(F̄)` is not the
trivial one.  Getting from *not trivial* to *onto* is a statement about the **order** of the target,
and that order is computed here for the first time on this front:
`Nat.card (rootsOfUnity n F) = n` over an algebraically closed `F` with `(n : F) ≠ 0`
(`natCard_rootsOfUnity_of_ne_zero`, one line off Mathlib's `HasEnoughRootsOfUnity`).  A nontrivial
homomorphism into a group of **prime** order has a nontrivial image, and a subgroup of a group of
prime order is `⊥` or `⊤`, so it is onto.

⚠️ **That last step is why this file stops at `n = 2` and `n = 3` and would not generalise even if
general `n` existed.**  At composite `n` the image can be a proper nontrivial subgroup and
surjectivity needs a genuinely different argument — the finite-abelian duality route sketched under
*Explicitly out of scope* below.  So general `n` is blocked here **twice over**, and only one of the
two obstructions is the pairing itself (see below).

⚠️ **The reason this used to give for general `n` was wrong** — it read *"only one of the two
obstructions is `#404`'s `ωₙ` crux"*.  `[n]∗` needs no `y`-coordinate division polynomial (`#1165`),
and the rung-5 root and the whole rung-6 translation slot are now stated at every `n`, with the
non-constancy side condition discharged at every `3`-smooth `n` (`#1304`, `#1308`).  What general
`n` waits on here is the **two-slot** pairing itself: `weilPairingN` and `weilPairingNHom` are names
this tree declares at no index but `2` and `3` (`WeilPairingFunctionTwo`,
`WeilPairingFunctionThree`, `#922`/`#925`), and the `[IsAlgClosed F]` they carry enters through
`hprin`, whose only producers are `exists_gS_{two,three}_of_isAlgClosed` (`#791`/`#825`).  ⚠️ *Twice
over* is untouched and is still right; only the first obstruction is renamed.

## `[IsAlgClosed F]` is used for a SECOND, independent reason here

Both function modules record that they carry `[IsAlgClosed F]` with no `_of_hprin` twin, because
their single gate *produces a witness* and `#899`'s test says base change never reaches those.  This
file inherits that gate and then uses `[IsAlgClosed F]` **again**, for something else entirely:
`μ_n(F)` has order `n` only when `F` contains a primitive `n`-th root of unity.  ⚠️ Over a
non-closed `F` the surjectivity statement below is not weaker, it is **false** — `e_2(S, ·)` cannot
be onto a two-element group whose second element is not in the field.  There is nothing here to
lift, and filing one would be the same error `WeilPairing.lean`'s scope section records for
non-degeneracy.

## Main statements

* `natCard_rootsOfUnity_of_ne_zero` — `#μ_n(F̄) = n`; a statement about a field, in the root
  namespace.
* `MonoidHom.surjective_of_ne_one_of_natCard_prime` — a nontrivial hom into a group of prime order
  is onto; a statement about groups, in the root namespace.
* `WeierstrassCurve.Affine.weilPairingTwoHom_apply_ne_one`, `…weilPairingThreeHom_apply_ne_one` —
  the slot map is nontrivial at a nonzero point; the only thing surjectivity takes from the merged
  kernel statement.
* `WeierstrassCurve.Affine.weilPairingTwo_surjective`, `…weilPairingThree_surjective`.
* `WeierstrassCurve.Affine.eq_zero_of_forall_weilPairingTwo_eq_one'`, `…Three…`.
* `WeierstrassCurve.Affine.ker_weilPairingTwoHom_flip`, `…Three…`.

## Naming and placement

The curve statements sit in `WeierstrassCurve.Affine` with `open CoordinateRing` — `#903`'s house
pattern, enforced tree-wide by `#918` and `#927`.  ⚠️ **The two general lemmas do not sit there.**
Neither mentions a Weierstrass curve, and putting a curve namespace on a curve-free statement is
`#903`'s defect one level up; they are stated at the root, above the namespace, and both belong
upstream in Mathlib rather than here.

## Explicitly out of scope

* **The perfect-pairing statement** — that `weilPairingTwoHom` is *bijective* onto
  `Multiplicative E[2] →* μ_2(F̄)`, identifying `E[n]` with its own dual.  ⚠️ **Landed**, as
  `EllipticCurves.FunctionField.WeilPairingPerfect` (`#940`), off
  `Mathlib.GroupTheory.FiniteAbelian.Duality`'s `card_monoidHom_of_hasEnoughRootsOfUnity`.  ⚠️ Two
  corrections to the route this bullet used to predict, kept because they are the reusable part:
  the `rootsOfUnity 2 F`-versus-`Fˣ` bridge is one `MonoidHom.codRestrict` and **not**
  `rootsOfUnityUnitsMulEquiv`, and `Monoid.exponent (Multiplicative E[2]) = 2` is **not** needed —
  `∀ g, g ^ n = 1` plus `HasEnoughRootsOfUnity.of_dvd` does the same job without having to rule out
  `E[2]` being trivial.  `card_torsion_two` turns out not to be needed either, except to name the
  number `4`.
* **General `n`** — see the two obstructions above.
* **The arbitrary-field (`_of_hprin`) form** — see the section above; the statement is false over a
  general field, so this is not a lift that has been skipped.
* **Galois-equivariance of the pairing function** — a separate front.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8, Prop. 8.1(d).
-/

/-- **`μ_n(F)` has exactly `n` elements** when `F` is algebraically closed and `n` is invertible in
`F`.  ⚠️ The hypothesis `(n : F) ≠ 0` is literally the `h2` / `h3` this front already carries, so no
new hypothesis appears at any call site — and it is the *only* hypothesis: `NeZero n` follows from
it rather than being asked for.

A statement about a field and nothing else; it belongs in Mathlib beside
`HasEnoughRootsOfUnity.natCard_rootsOfUnity`, which is its whole proof once the `NeZero` instance is
supplied. -/
theorem natCard_rootsOfUnity_of_ne_zero {F : Type*} [Field F] [IsAlgClosed F] {n : ℕ}
    (hn : (n : F) ≠ 0) : Nat.card (rootsOfUnity n F) = n := by
  haveI : NeZero n := ⟨fun h => hn (by simp [h])⟩
  haveI : NeZero ((n : ℕ) : F) := ⟨hn⟩
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity F n

/-- **A nontrivial homomorphism into a group of prime order is surjective.**  Its image is a
subgroup, and a group of prime order has only the two trivial ones.

A statement about groups and nothing else; it belongs in Mathlib beside
`Subgroup.eq_bot_or_eq_top_of_prime_card`, which is its whole proof. -/
theorem MonoidHom.surjective_of_ne_one_of_natCard_prime {G H : Type*} [Group G] [Group H] {p : ℕ}
    (hp : p.Prime) (hcard : Nat.card H = p) {φ : G →* H} (hφ : φ ≠ 1) : Function.Surjective φ := by
  haveI : Fact (Nat.card H).Prime := ⟨hcard ▸ hp⟩
  rcases φ.range.eq_bot_or_eq_top_of_prime_card with h | h
  · exact absurd (MonoidHom.ext fun g => by
      simpa using (Subgroup.mem_bot).mp (h ▸ MonoidHom.mem_range.mpr ⟨g, rfl⟩)) hφ
  · exact MonoidHom.range_eq_top.mp h

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] [IsAlgClosed F] {W : Affine F} [W.IsElliptic]

/-! ### `n = 2` -/

open Classical in
/-- **The slot map `e_2(S, ·)` is nontrivial for `S ≠ 0`**, read off the trivial kernel of the
bundled pairing.  This is the only thing surjectivity needs from non-degeneracy. -/
theorem weilPairingTwoHom_apply_ne_one (h2 : (2 : F) ≠ 0) {S : W.torsion 2} (hS : S ≠ 0) :
    weilPairingTwoHom h2 (Multiplicative.ofAdd S) ≠ 1 := fun h => hS (by
  have hmem : (Multiplicative.ofAdd S) ∈ MonoidHom.ker (weilPairingTwoHom (W := W) h2) :=
    MonoidHom.mem_ker.mpr h
  rw [ker_weilPairingTwoHom h2, Subgroup.mem_bot] at hmem
  simpa using hmem)

open Classical in
/-- **Surjectivity at `n = 2`**: for `S ≠ 0` the map `T ↦ e_2(S, T)` hits every square root of
unity, so in particular `e_2(S, T) = −1` for some `T ∈ E[2]`.

⚠️ The image is a subgroup of a group of order `2` (`natCard_rootsOfUnity_of_ne_zero`), and it is
not trivial (`weilPairingTwoHom_apply_ne_one`), so it is everything.  Both halves are needed: the
kernel statement alone gives only *some* value `≠ 1`. -/
theorem weilPairingTwo_surjective (h2 : (2 : F) ≠ 0) {S : W.torsion 2} (hS : S ≠ 0) :
    Function.Surjective (weilPairingTwo h2 S) := fun ζ => by
  obtain ⟨T, hT⟩ := MonoidHom.surjective_of_ne_one_of_natCard_prime Nat.prime_two
    (natCard_rootsOfUnity_of_ne_zero (F := F) (n := 2) h2)
    (weilPairingTwoHom_apply_ne_one h2 hS) ζ
  exact ⟨T.toAdd, hT⟩

open Classical in
/-- **Non-degeneracy in the second slot at `n = 2`.**  The merged form fixes `S` and quantifies `T`;
this fixes `T` and quantifies `S`, which is one antisymmetry rewrite away and is what the flipped
bundled map needs. -/
theorem eq_zero_of_forall_weilPairingTwo_eq_one' (h2 : (2 : F) ≠ 0) {T : W.torsion 2}
    (hone : ∀ S : W.torsion 2, weilPairingTwo h2 S T = 1) : T = 0 :=
  eq_zero_of_forall_weilPairingTwo_eq_one h2 fun S => by
    rw [weilPairingTwo_swap h2, hone S, inv_one]

open Classical in
/-- **The flipped bundled pairing has trivial kernel too**: `MonoidHom.ker (e_2)ᵀ = ⊥`.  The
`MonoidHom.ext` distance from `eq_zero_of_forall_weilPairingTwo_eq_one'` is exactly the packaging,
as it is for `ker_weilPairingTwoHom`. -/
theorem ker_weilPairingTwoHom_flip (h2 : (2 : F) ≠ 0) :
    MonoidHom.ker (weilPairingTwoHom (W := W) h2).flip = ⊥ := by
  refine le_antisymm (fun T hT => ?_) bot_le
  rw [Subgroup.mem_bot]
  rw [MonoidHom.mem_ker] at hT
  have hval : ∀ S : W.torsion 2, weilPairingTwo h2 S T.toAdd = 1 := fun S => by
    have hS := congrArg (fun φ => φ (Multiplicative.ofAdd S)) hT
    simpa using hS
  simpa using eq_zero_of_forall_weilPairingTwo_eq_one' h2 hval

/-! ### `n = 3` -/

open Classical in
/-- **The slot map `e_3(S, ·)` is nontrivial for `S ≠ 0`**, the `n = 3` mirror. -/
theorem weilPairingThreeHom_apply_ne_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {S : W.torsion 3} (hS : S ≠ 0) :
    weilPairingThreeHom h2 h3 (Multiplicative.ofAdd S) ≠ 1 := fun h => hS (by
  have hmem : (Multiplicative.ofAdd S) ∈ MonoidHom.ker (weilPairingThreeHom (W := W) h2 h3) :=
    MonoidHom.mem_ker.mpr h
  rw [ker_weilPairingThreeHom h2 h3, Subgroup.mem_bot] at hmem
  simpa using hmem)

open Classical in
/-- **Surjectivity at `n = 3`**: for `S ≠ 0` the map `T ↦ e_3(S, T)` hits every cube root of unity,
so in particular a *primitive* one.

⚠️ The cardinality of `μ_3(F̄)` is gated on `h3`, not on `h2`.  `h2` is still genuinely needed here,
inherited from `weilPairingThree` itself, where it enters through the doubling slope rather than
through `mulByThreeEndo`; neither hypothesis is decorative. -/
theorem weilPairingThree_surjective (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {S : W.torsion 3} (hS : S ≠ 0) : Function.Surjective (weilPairingThree h2 h3 S) := fun ζ => by
  obtain ⟨T, hT⟩ := MonoidHom.surjective_of_ne_one_of_natCard_prime Nat.prime_three
    (natCard_rootsOfUnity_of_ne_zero (F := F) (n := 3) h3)
    (weilPairingThreeHom_apply_ne_one h2 h3 hS) ζ
  exact ⟨T.toAdd, hT⟩

open Classical in
/-- **Non-degeneracy in the second slot at `n = 3`.** -/
theorem eq_zero_of_forall_weilPairingThree_eq_one' (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {T : W.torsion 3} (hone : ∀ S : W.torsion 3, weilPairingThree h2 h3 S T = 1) : T = 0 :=
  eq_zero_of_forall_weilPairingThree_eq_one h2 h3 fun S => by
    rw [weilPairingThree_swap h2 h3, hone S, inv_one]

open Classical in
/-- **The flipped bundled pairing has trivial kernel at `n = 3` too.** -/
theorem ker_weilPairingThreeHom_flip (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    MonoidHom.ker (weilPairingThreeHom (W := W) h2 h3).flip = ⊥ := by
  refine le_antisymm (fun T hT => ?_) bot_le
  rw [Subgroup.mem_bot]
  rw [MonoidHom.mem_ker] at hT
  have hval : ∀ S : W.torsion 3, weilPairingThree h2 h3 S T.toAdd = 1 := fun S => by
    have hS := congrArg (fun φ => φ (Multiplicative.ofAdd S)) hT
    simpa using hS
  simpa using eq_zero_of_forall_weilPairingThree_eq_one' h2 h3 hval

/-! ### Non-vacuity

Everything above carries `[IsAlgClosed F]` and `[W.IsElliptic]`, so `ℚ` cannot witness it.  The
curves are the ones the two function modules already name — `y² = x³ − x` at `n = 2` and
`y² + y = x³` at `n = 3`, both over `AlgebraicClosure ℚ` — and in each case the torsion point is
**named**: `S = (0, 0)`.

⚠️ **The load-bearing certificates are the surjectivity ones, and this file can show that they are
rather than assert it.**  Substituting `S := 0` makes surjectivity *false*, not merely unprovable:
`weilPairingTwo h2 0` is constantly `1` while `μ_2(F̄)` has two elements, and the refutation is
compiled below as `not_surjective_weilPairingTwo_zero`.  ⚠️ Note what that costs: the refutation
needs `natCard_rootsOfUnity_of_ne_zero`, i.e. the *same* new input surjectivity needs — so the two
`example`s together certify that the input is doing work in both directions.

The flipped-kernel certificate is the weightless one: it instantiates a universally quantified
equation at a curve, so it certifies that the construction elaborates and nothing more (`#916`). -/

section Nonvacuity

/-- An algebraically closed field of characteristic zero. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

private lemma exampleTwo : (2 : exampleField) ≠ 0 := by norm_num

private lemma exampleThree : (3 : exampleField) ≠ 0 := by norm_num

/-- The curve `y² = x³ − x` over `AlgebraicClosure ℚ`, this tree's `n = 2` certificate curve. -/
private noncomputable def exampleCurveTwo : Affine exampleField := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurveTwo.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurveTwo, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- `S = (0, 0)` lies on `y² = x³ − x` and is nonsingular. -/
private lemma exampleNonsingularTwo : exampleCurveTwo.Nonsingular 0 0 :=
  exampleCurveTwo.equation_iff_nonsingular.mp (by
    norm_num [exampleCurveTwo, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `S = (0, 0)` is `2`-torsion. -/
private lemma exampleTorsionTwo :
    Point.some (0 : exampleField) 0 exampleNonsingularTwo ∈ exampleCurveTwo.torsion 2 :=
  (mem_torsion_two_some_iff exampleNonsingularTwo).mpr (by norm_num [exampleCurveTwo])

open Classical in
/-- The named `2`-torsion point, as an element of `E[2]`. -/
private noncomputable def exampleSTwo : exampleCurveTwo.torsion 2 :=
  ⟨Point.some 0 0 exampleNonsingularTwo, exampleTorsionTwo⟩

open Classical in
private lemma exampleSTwo_ne_zero : exampleSTwo ≠ 0 := fun h =>
  Point.some_ne_zero exampleNonsingularTwo (congrArg Subtype.val h)

open Classical in
/-- **The load-bearing certificate at `n = 2`**: at the named point `S = (0, 0)` of `y² = x³ − x`,
every square root of unity is a pairing value. -/
example : Function.Surjective (weilPairingTwo exampleTwo exampleSTwo) :=
  weilPairingTwo_surjective exampleTwo exampleSTwo_ne_zero

open Classical in
/-- **Why the certificate above is load-bearing**: the same statement at `S = 0` is *false*, so its
truth turns on the point being the named non-trivial one and not on the construction elaborating.
⚠️ This is a refutation, not a failed proof attempt — it is checked by the build. -/
private theorem not_surjective_weilPairingTwo_zero :
    ¬ Function.Surjective (weilPairingTwo (W := exampleCurveTwo) exampleTwo 0) := by
  intro hsurj
  have hone : ∀ ζ : rootsOfUnity 2 exampleField, ζ = 1 := fun ζ => by
    obtain ⟨T, hT⟩ := hsurj ζ
    rw [← hT, weilPairingTwo_zero_left]
  have hcard : Nat.card (rootsOfUnity 2 exampleField) = 2 :=
    natCard_rootsOfUnity_of_ne_zero (F := exampleField) (n := 2) exampleTwo
  haveI : Subsingleton (rootsOfUnity 2 exampleField) := ⟨fun a b => (hone a).trans (hone b).symm⟩
  rw [Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩] at hcard
  exact absurd hcard (by norm_num)

open Classical in
/-- The flipped bundled map exists on that curve and its kernel is trivial — an instance of a
universally quantified equation, and the weightless certificate of the three. -/
example : MonoidHom.ker (weilPairingTwoHom (W := exampleCurveTwo) exampleTwo).flip = ⊥ :=
  ker_weilPairingTwoHom_flip exampleTwo

/-- The curve `y² + y = x³` over `AlgebraicClosure ℚ`, this tree's `n = 3` certificate curve.
⚠️ `y² = x³ − x` would not serve at `n = 3`: its `Ψ₃` has no rational root, so none of its nine
`3`-torsion points can be named. -/
private noncomputable def exampleCurveThree : Affine exampleField := ⟨0, 0, 1, 0, 0⟩

private instance : exampleCurveThree.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurveThree, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- `S = (0, 0)` lies on `y² + y = x³` and is nonsingular. -/
private lemma exampleNonsingularThree : exampleCurveThree.Nonsingular 0 0 :=
  exampleCurveThree.equation_iff_nonsingular.mp (by
    norm_num [exampleCurveThree, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `S = (0, 0)` is `3`-torsion: `Ψ₃ = 3X⁴ + 3b₆X` vanishes at `0`. -/
private lemma exampleTorsionThree :
    Point.some (0 : exampleField) 0 exampleNonsingularThree ∈ exampleCurveThree.torsion 3 :=
  mem_torsion_three_some_iff'.mpr (by
    norm_num [exampleCurveThree, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈])

open Classical in
/-- The named `3`-torsion point, as an element of `E[3]`. -/
private noncomputable def exampleSThree : exampleCurveThree.torsion 3 :=
  ⟨Point.some 0 0 exampleNonsingularThree, exampleTorsionThree⟩

open Classical in
private lemma exampleSThree_ne_zero : exampleSThree ≠ 0 := fun h =>
  Point.some_ne_zero exampleNonsingularThree (congrArg Subtype.val h)

open Classical in
/-- **The load-bearing certificate at `n = 3`**: at the named point `S = (0, 0)` of `y² + y = x³`,
every cube root of unity is a pairing value — in particular a primitive one. -/
example : Function.Surjective (weilPairingThree exampleTwo exampleThree exampleSThree) :=
  weilPairingThree_surjective exampleTwo exampleThree exampleSThree_ne_zero

open Classical in
/-- **Why the certificate above is load-bearing**: at `S = 0` it is false, for the same reason as at
`n = 2` and with `3` for `2`. -/
private theorem not_surjective_weilPairingThree_zero :
    ¬ Function.Surjective
      (weilPairingThree (W := exampleCurveThree) exampleTwo exampleThree 0) := by
  intro hsurj
  have hone : ∀ ζ : rootsOfUnity 3 exampleField, ζ = 1 := fun ζ => by
    obtain ⟨T, hT⟩ := hsurj ζ
    rw [← hT, weilPairingThree_zero_left]
  have hcard : Nat.card (rootsOfUnity 3 exampleField) = 3 :=
    natCard_rootsOfUnity_of_ne_zero (F := exampleField) (n := 3) exampleThree
  haveI : Subsingleton (rootsOfUnity 3 exampleField) := ⟨fun a b => (hone a).trans (hone b).symm⟩
  rw [Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩] at hcard
  exact absurd hcard (by norm_num)

open Classical in
/-- The flipped bundled map at `n = 3`, on that curve. -/
example :
    MonoidHom.ker (weilPairingThreeHom (W := exampleCurveThree) exampleTwo exampleThree).flip = ⊥ :=
  ker_weilPairingThreeHom_flip exampleTwo exampleThree

end Nonvacuity

end WeierstrassCurve.Affine
