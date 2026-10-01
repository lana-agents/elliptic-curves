/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.OddTorsionCountSplits
import EllipticCurves.Torsion.StructureGeneral
import EllipticCurves.Torsion.ThreeTorsionStructure
import EllipticCurves.Torsion.XSupport

/-!
# `#E[n] = n²` at even `n` over a field that is not algebraically closed

`EllipticCurves.Torsion.OddTorsionCountSplits` gives the closure-free `*_of_splits` family its
general-`n` member at **odd** `n`, and records in terms that the even case is a different statement
rather than that one with a binder deleted: *"its relation carries a `#{roots of Ψ₂Sq}` term and
needs `IsCoprime (W.preΨ n) W.Ψ₂Sq`, which this tree does not have."*  This file supplies the even
member, and `card_torsion_eq_sq_of_splits_of_splits_Ψ₂Sq` below joins the two into the general-`n`
member with no parity hypothesis at all.

## The relation, and the two terms the odd one does not have

```
odd  n :  #E[n] = 2 · #{roots of preΨₙ} + 1                      = 2·(n² − 1)/2 + 1     = n²
even n :  #E[n] = 2 · #{roots of preΨₙ} + #{roots of Ψ₂Sq} + 1   = 2·(n² − 4)/2 + 3 + 1 = n²
```

`ΨSqₙ = preΨₙ² · Ψ₂Sq` at even `n` by Mathlib's definition, so the `x`-support of `E[n] \ {O}` is
the roots of `preΨₙ` **together with** the roots of `Ψ₂Sq`, and the fibre over a root of `Ψ₂Sq` is a
**singleton** rather than a pair — the discriminant of the Weierstrass quadratic in `y` vanishes
there, so `y = −(a₁x + a₃)/2` is its only solution and it is already in `F`.  ⚠️ **The second
arithmetic is right only if the two root sets are DISJOINT**, and that is the ingredient `#2307` was
filed to price.

## ⚠️⚠️ Both missing ingredients are THEOREMS, and ⚠️ **one argument supplies both**

⚠️ **Neither is a hypothesis of any statement below.** `#2307` asks for the disjointness *"in the
shape the proof needs"* and asks *"whether it is a hypothesis of the headline or a theorem
discharged inside it"*, with the note that *"if it is a hypothesis, the headline is weaker than the
odd form in a way a reader must be told about."*  ⚠️ **It is a theorem, in both of the shapes that
row names**, so the even headline is exactly as strong as the odd one and `#2296`'s ladder needs to
be told nothing:

* `isCoprime_preΨ_Ψ₂Sq_of_even` : `IsCoprime (W.preΨ n) W.Ψ₂Sq` at even `n` — the shape of the whole
  `EllipticCurves.DivisionPolynomial.Coprime` family, and the one `#2307`'s table of near misses is
  written in;
* `eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero_of_even` : the pointwise shape, which is what the count
  below actually consumes.

⚠️ **And the engine is not a new argument about multiplicities.  It is the SHARP UPPER BOUND MEETING
THE CLOSED COUNT, with no slack left over.**  Over `AlgebraicClosure F`, write `A` for the roots of
`preΨₙ` and `B` for the roots of `Ψ₂Sq`.  Feeding `A \ B` and `B` to
`EllipticCurves.Torsion.Finite`'s `card_torsion_le_of_xCoords_of_selfNeg` — rather than `A` and `B`,
which is what the `≤ n²` of `EllipticCurves.Torsion.XSupport` does — gives

```
n² = #E[n] ≤ 2·|A \ B| + |B| + 1 = 2·|A \ B| + 4 ≤ 2·|A| + 4 ≤ 2·deg preΨₙ + 4 = n²
```

using `card_torsion_eq_sq` on the left and `card_roots_Ψ₂Sq` for `|B| = 3`.  ⚠️ **Every
inequality in that chain is therefore an equality**, and the two of them that are not arithmetic
are exactly the two ingredients: `|A \ B| = |A|` is the disjointness, and `|A| = deg preΨₙ` is
separability.  Both then descend to an arbitrary `F` — a common root in `F` is a common root in
the closure, and `Polynomial.separable_map` carries separability down — so neither statement keeps
the closure it was proved with.

⚠️ **This is why `natDegree_preΨ` being EXACT rather than `_le` is load-bearing**, and
`EllipticCurves.Torsion.XSupport` does not need it: an upper bound on `#E[n]` is happy with
`natDegree_preΨ_le`, while the chain above collapses only because its last step is an equality.

## ⚠️ What `#2307` predicted about the second ingredient, and how the route here differs

That row's pricing comment identifies the second missing ingredient as *"an even-`n` or general-`n`
`#E[n] = n² ↔ Separable (preΨ n)` BRIDGE"*, on the ground that
`card_torsion_eq_sq_iff_separable_preΨ` (`EllipticCurves.Torsion.OddTorsionCount`) binds `Odd n` and
that all six `Separable (preΨ …)` members in the tree are `Odd`-gated or at a fixed odd index.  ⚠️
**Both halves of that census are correct and this file does not build the bridge.**  The `↔` is
still `Odd`-gated, and nothing here widens it: the chain above uses the counting *bound* instead, so
separability comes out of `card_torsion_le_of_xCoords_of_selfNeg` and `card_torsion_eq_sq` and never
passes through an iff.  ⚠️ **So the ingredient the row named as missing is still missing, and it
turned out not to be needed** — `separable_preΨ` below is the general-`n` separability statement the
row wanted, reached by a route the row did not consider.

## ⚠️ `n = 2` is an instance of the even form, and that is the asymmetry with the odd one

`EllipticCurves.Torsion.OddTorsionCountSplits` carries a one-line `example` measuring
`W.preΨ 2 = 1`, and concludes that `card_torsion_two_of_splits`
(`EllipticCurves.Torsion.TwoTorsion`) *"is not an instance of anything above"*: at `n = 2` the odd
form's two hypotheses are vacuously true — a unit splits and has no roots — while `#E[2] = 4` is
false over a general field.  ⚠️ **The even form admits `n = 2` for exactly the reason the odd one
cannot**: the whole count is carried by
the `#{roots of Ψ₂Sq}` term, `preΨ₂ = 1` contributes no roots, and the surviving hypothesis is
`W.Ψ₂Sq.Splits` — which is `card_torsion_two_of_splits`' only hypothesis.  The recovery is an
`example` below, and the `ℚ` certificate under `### Non-vacuity` is that `example` on a curve.

## ⚠️ Non-vacuity, and what is NOT certified

`### Non-vacuity` below proves `#E[2] = 4` for `y² = x(x + 1)(x + 4)` over `ℚ` **from the even form
of this file**, with no hypothesis and no algebraic closure anywhere.  ⚠️ **That is a certificate at
one even index and it is not a certificate at the others.**  Measured rather than asserted: the even
headline at `n = 4` additionally needs `(W.preΨ 4).Splits`, a degree-`6` condition, and
`E(F) ⊇ (ℤ/4)²` forces `4 ∣ #μ(F)` — so the `ℚ` route is barred by the same `μₙ ⊆ F` obstruction
that `EllipticCurves.Torsion.ThreeTorsionSplitCertificate` records at `n = 3` and a finite base is
needed.  ⚠️ **That obstruction argument is classical and is formalised NOWHERE in this tree**; it is
named here as the reason no `n ≥ 4` certificate is shipped and must not be cited as a theorem of the
repository.

## ⚠️ Three private helpers are replicated rather than imported, and the count is the finding

Each is `private` in a file this one imports directly, so none can be consumed:

* `ncard_setOf_isRoot_le'` re-proves `EllipticCurves.Torsion.XSupport`'s `ncard_setOf_isRoot_le`;
* `algebraMap_natCast_ne_zero'` re-proves `EllipticCurves.Torsion.OddTorsionCountSplits`' lemma of
  that name — which is itself the file this one is the sibling of;
* `four_ne_zero'` re-proves a `(2 : F) ≠ 0 → (4 : F) ≠ 0` step that is ⚠️ **already `private` in
  SEVEN files** (`FunctionField/MulByTwoDegree`, `FunctionField/MulByTwoFibreInfinity`,
  `FunctionField/MulByTwoPlaceAtInfinity`, `Torsion/HalvingExtension`, `Torsion/TwoTorsion`,
  `Torsion/TwoTorsionSplittingField`, `Torsion/XSupport`), under four different names.  **This file
  is the eighth copy.**

⚠️ **All three are named here rather than repaired**, on `#2250` round 2's report-rather-than-
route-around standard: dropping `private` is a change to another module's interface and this row is
scoped to the even-`n` count.  ⚠️ **The third one is the one worth a row of its own** — seven copies
under four names is not a local duplication, and one public `(4 : F) ≠ 0` helper retires all eight.

## Main definitions

* `WeierstrassCurve.Affine.torsionEvenOfPair`, `WeierstrassCurve.Affine.torsionEvenPairEquiv` :
  `E[n] ≃ Option ((Σ root of preΨₙ, fibre) ⊕ (Σ root of Ψ₂Sq, fibre))` at even `n`.  ⚠️ A **sum**
  of two sigmas, and it is a bijection only because the two root sets are disjoint.

## Main statements

* `WeierstrassCurve.Affine.isCoprime_preΨ_Ψ₂Sq_of_even`,
  `WeierstrassCurve.Affine.eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero_of_even` : the disjointness, in
  the two shapes `#2307` asks for, at even `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`.
* `WeierstrassCurve.Affine.separable_preΨ_of_even` : `Separable (W.preΨ n)` at even `n` with
  `(2 : F) ≠ 0` and `(n : F) ≠ 0`, over **any** field.
* `WeierstrassCurve.Affine.separable_preΨ` : the same at **every** `n`, no parity hypothesis.
* `WeierstrassCurve.Affine.card_setOf_equation_eq_one_of_eval_Ψ₂Sq_eq_zero` : the fibre over a root
  of `Ψ₂Sq` is a singleton, with `(2 : F) ≠ 0`.
* `WeierstrassCurve.Affine.card_roots_preΨ_of_splits_of_even` : `#{roots of preΨₙ} = (n² − 4)/2`.
* `WeierstrassCurve.Affine.card_torsion_even_of_isSquare` : the relation
  `#E[n] = 2 · #{roots of preΨₙ} + #{roots of Ψ₂Sq} + 1`.
* **`WeierstrassCurve.Affine.card_torsion_eq_sq_of_splits_of_even`** : `#E[n] = n²` at even `n`.
* **`WeierstrassCurve.Affine.card_torsion_eq_sq_of_splits_of_splits_Ψ₂Sq`** : `#E[n] = n²` at
  **every** `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0` over which `preΨₙ` and `Ψ₂Sq` both split and
  `Ψ₂Sq` is a square at every root of `preΨₙ` — the general-`n` member of the closure-free family.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6, Corollary 6.4.
-/

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-- `(4 : F) ≠ 0` from `(2 : F) ≠ 0`.  ⚠️ The eighth private copy of this step in the tree; see the
module docstring, which names the other seven. -/
private lemma four_ne_zero' (h2 : (2 : F) ≠ 0) : (4 : F) ≠ 0 := by
  rw [show (4 : F) = 2 * 2 by norm_num]
  exact mul_ne_zero h2 h2

/-- A natural number nonzero in `F` stays nonzero in any `F`-algebra that is a field.  ⚠️ A copy of
`EllipticCurves.Torsion.OddTorsionCountSplits`' lemma of this name, which is `private` there. -/
private lemma algebraMap_natCast_ne_zero' {L : Type*} [Field L] [Algebra F L] {n : ℕ}
    (h : (n : F) ≠ 0) : (n : L) ≠ 0 := by
  rw [← map_natCast (algebraMap F L) n, ne_eq, map_eq_zero]
  exact h

/-- A nonzero polynomial over a field has at most `natDegree` many distinct roots.  ⚠️ A copy of
`EllipticCurves.Torsion.XSupport`'s `ncard_setOf_isRoot_le`, which is `private` there. -/
private lemma ncard_setOf_isRoot_le' {p : F[X]} (hp : p ≠ 0) :
    {x : F | p.IsRoot x}.ncard ≤ p.natDegree := by
  classical
  have h : {x : F | p.IsRoot x}.ncard = p.roots.toFinset.card := by
    rw [← card_root_subtype hp, ← Nat.card_coe_set_eq]
    rfl
  rw [h]
  exact (Multiset.toFinset_card_le _).trans p.card_roots'

/-- `2 · (n² − 4)/2 + 3 + 1 = n²` at even `n ≠ 0`, in `ℕ` with truncated subtraction and division.

⚠️ **The even-`n` counterpart of `EllipticCurves.Torsion.OddTorsionCount`'s
`two_mul_pred_sq_div_two_add_one`, and not a copy of it**: that one is
`2 · (n² − 1)/2 + 1 = n²` at odd `n`.  The `n ≠ 0` hypothesis is not decoration — at `n = 0` the
left side is `4` and the right side is `0`, because `0² − 4` truncates to `0`. -/
private lemma two_mul_sq_sub_four_div_two_add_four {n : ℕ} (heven : Even n) (hn : n ≠ 0) :
    2 * ((n ^ 2 - 4) / 2) + 3 + 1 = n ^ 2 := by
  obtain ⟨m, rfl⟩ := heven
  have hm : 1 ≤ m := by omega
  have hsq : (m + m) ^ 2 = 4 * m ^ 2 := by ring
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm
  rw [hsq]
  omega

/-! ### The closure core: the sharp bound meets the closed count

⚠️ **Both of the even-`n` ingredients come out of ONE argument and are proved together**, because
they are two of the equalities forced by the same chain having no slack.  Splitting them into two
lemmas would run that chain twice and would invite a reader to think the second is a corollary of
the first, which it is not. -/

/-- **Over an algebraically closed field, at even `n` the roots of `preΨₙ` avoid the roots of `Ψ₂Sq`
and `preΨₙ` is separable**, for an elliptic curve with `(2 : F) ≠ 0` and `(n : F) ≠ 0`.

The chain is in the module docstring: `card_torsion_le_of_xCoords_of_selfNeg` fed with `A \ B` and
`B` rather than `A` and `B`, against `card_torsion_eq_sq` on the other side, with `|B| = 3` from
`card_roots_Ψ₂Sq` and `|A| ≤ deg preΨₙ = (n² − 4)/2` from the **exact** `natDegree_preΨ`.  The two
ends agree, so `|A \ B| = |A|` and `|A| = deg preΨₙ`.

⚠️ **`A \ B` is the only choice of `S` that makes the bound sharp enough to see the disjointness.**
With `S = A` the chain reads `n² ≤ 2|A| + 3 + 1 ≤ n²`, which still forces `|A| = deg preΨₙ` and so
still gives separability, but says nothing at all about `A ∩ B`: the engine would be charging two
points to a root it had already charged one point to, and the resulting slack is exactly the
quantity the disjointness is about. -/
private lemma disjoint_and_separable_preΨ_of_even_of_isAlgClosed [IsAlgClosed F]
    [W.IsElliptic] (h2 : (2 : F) ≠ 0) {n : ℕ} (heven : Even n) (hn : (n : F) ≠ 0) :
    (∀ x : F, (W.preΨ (n : ℤ)).eval x = 0 → W.Ψ₂Sq.eval x ≠ 0) ∧
      (W.preΨ (n : ℤ)).Separable := by
  classical
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hn' : ((n : ℤ) : F) ≠ 0 := by exact_mod_cast hn
  have hp : W.preΨ (n : ℤ) ≠ 0 := W.preΨ_ne_zero hn'
  have hq : W.Ψ₂Sq ≠ 0 := W.Ψ₂Sq_ne_zero (four_ne_zero' h2)
  set A : Set F := {x : F | (W.preΨ (n : ℤ)).IsRoot x} with hA
  set B : Set F := {x : F | W.Ψ₂Sq.IsRoot x} with hB
  have hAfin : A.Finite := finite_setOf_isRoot hp
  have hBfin : B.Finite := finite_setOf_isRoot hq
  have hdeg : (W.preΨ (n : ℤ)).natDegree = (n ^ 2 - 4) / 2 := by
    rw [W.natDegree_preΨ hn', if_pos (by exact_mod_cast heven : Even ((n : ℤ)))]
    simp
  have hBcard : B.ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    exact card_roots_Ψ₂Sq h2
  have hAle : A.ncard ≤ (n ^ 2 - 4) / 2 := hdeg ▸ ncard_setOf_isRoot_le' hp
  -- The sharp bound, with the roots of `preΨₙ` that are also roots of `Ψ₂Sq` removed from the
  -- part that is charged two points per fibre.
  have hbound := W.card_torsion_le_of_xCoords_of_selfNeg (n := n)
    (show (A \ B).Finite from hAfin.sdiff) hBfin
    (fun _ _ _ hP => by
      rw [hA, hB, Set.sdiff_union_self]
      exact mem_preΨ_union_Ψ₂Sq_of_mem_torsion h2 hP)
    (fun _ _ hns _ hx => selfNeg_of_isRoot_Ψ₂Sq hns.left hx)
  rw [card_torsion_eq_sq h2 hn, hBcard] at hbound
  have hdiffle : (A \ B).ncard ≤ A.ncard := Set.ncard_le_ncard Set.sdiff_subset hAfin
  have harith := two_mul_sq_sub_four_div_two_add_four heven hn0
  have hAeq : A.ncard = (n ^ 2 - 4) / 2 := by omega
  have hsub : A \ B ⊆ A := Set.sdiff_subset
  have hAB : A \ B = A := Set.eq_of_subset_of_ncard_le hsub (by omega) hAfin
  refine ⟨fun x hx hx2 => ?_, ?_⟩
  · have hxA : x ∈ A := hx
    rw [← hAB] at hxA
    exact hxA.2 hx2
  · have hsplits : (W.preΨ (n : ℤ)).Splits := IsAlgClosed.splits _
    refine (nodup_roots_iff_of_splits hp hsplits).mp ?_
    rw [← Multiset.toFinset_card_eq_card_iff_nodup]
    have hroots : (W.preΨ (n : ℤ)).roots.toFinset.card = A.ncard := by
      rw [← card_root_subtype hp, ← Nat.card_coe_set_eq]
      rfl
    rw [hroots, hAeq, splits_iff_card_roots.mp hsplits, hdeg]

/-! ### The descent: both ingredients over an arbitrary field -/

/-- **At an even index, a root of `preΨₙ` is not a root of `Ψ₂Sq`**, for an elliptic curve over any
field with `(2 : F) ≠ 0` and `(n : F) ≠ 0`.

The descent is the cheap direction of the problem: a common root in `F` maps to a common root in
`AlgebraicClosure F`, where `disjoint_and_separable_preΨ_of_even_of_isAlgClosed` refutes it.  No
statement about `F` is lost, because the hypothesis under refutation is about a single element.

⚠️ **This is the even-`n` counterpart of
`EllipticCurves.Torsion.OddTorsionCountSplits`' `eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero'` and the
two are proved by unrelated arguments.**  At odd `n` the statement is elementary — a common root
carries a `2`-torsion point and `ψ` does not vanish at an odd index at a `2`-torsion point — and ⚠️
**that step is FALSE at even `n`**, since a `2`-torsion point *is* `n`-torsion when `n` is even, so
`ψₙ` does vanish there.  The even case is the counting argument instead, and it binds
`(n : F) ≠ 0`, which the odd one does not. -/
theorem eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero_of_even [W.IsElliptic] (h2 : (2 : F) ≠ 0) {n : ℕ}
    (heven : Even n) (hn : (n : F) ≠ 0) {x : F} (hx : (W.preΨ (n : ℤ)).eval x = 0) :
    W.Ψ₂Sq.eval x ≠ 0 := by
  classical
  intro hx2
  haveI : (W⁄(AlgebraicClosure F)).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F (AlgebraicClosure F))).IsElliptic
  have h2' : (2 : AlgebraicClosure F) ≠ 0 := by
    simpa using algebraMap_natCast_ne_zero' (L := AlgebraicClosure F) (n := 2) (by simpa using h2)
  have hn' : ((n : ℕ) : AlgebraicClosure F) ≠ 0 := algebraMap_natCast_ne_zero' hn
  refine (disjoint_and_separable_preΨ_of_even_of_isAlgClosed (W := W⁄(AlgebraicClosure F))
    h2' heven hn').1 (algebraMap F (AlgebraicClosure F) x) ?_ ?_
  · rw [show (W⁄(AlgebraicClosure F)).preΨ (n : ℤ)
        = (W.preΨ (n : ℤ)).map (algebraMap F (AlgebraicClosure F)) from map_preΨ ..,
      eval_map, eval₂_at_apply, hx, map_zero]
  · rw [show (W⁄(AlgebraicClosure F)).Ψ₂Sq
        = W.Ψ₂Sq.map (algebraMap F (AlgebraicClosure F)) from map_Ψ₂Sq ..,
      eval_map, eval₂_at_apply, hx2, map_zero]

/-- **`IsCoprime (preΨₙ) Ψ₂Sq` at even `n`**, for an elliptic curve over any field with
`(2 : F) ≠ 0` and `(n : F) ≠ 0`.

⚠️ **This is the shape `#2307`'s table of near misses is written in, and it is strictly stronger
than the pointwise form above**: having no common root *in `F`* does not imply coprimality, since a
common factor may be irreducible over `F`.  What closes the gap is that the core lemma rules out a
common root over `AlgebraicClosure F`, which is what
`Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed` asks for.

The tree's `EllipticCurves.DivisionPolynomial.Coprime` family has six `IsCoprime`-concluding
members and ⚠️ **none of them pairs `preΨ n` with `Ψ₂Sq` at any parity** — `isCoprime_Ψ₃_Ψ₂Sq` is
the `n = 3` instance of the odd fact, and `isCoprime_preΨ₄_Ψ₃` is an even-index `preΨ` against the
wrong right-hand side. -/
theorem isCoprime_preΨ_Ψ₂Sq_of_even [W.IsElliptic] (h2 : (2 : F) ≠ 0) {n : ℕ} (heven : Even n)
    (hn : (n : F) ≠ 0) : IsCoprime (W.preΨ (n : ℤ)) W.Ψ₂Sq := by
  classical
  haveI : (W⁄(AlgebraicClosure F)).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F (AlgebraicClosure F))).IsElliptic
  have h2' : (2 : AlgebraicClosure F) ≠ 0 := by
    simpa using algebraMap_natCast_ne_zero' (L := AlgebraicClosure F) (n := 2) (by simpa using h2)
  have hn' : ((n : ℕ) : AlgebraicClosure F) ≠ 0 := algebraMap_natCast_ne_zero' hn
  have hmapp : (W⁄(AlgebraicClosure F)).preΨ (n : ℤ)
      = (W.preΨ (n : ℤ)).map (algebraMap F (AlgebraicClosure F)) := map_preΨ ..
  have hmapq : (W⁄(AlgebraicClosure F)).Ψ₂Sq
      = W.Ψ₂Sq.map (algebraMap F (AlgebraicClosure F)) := map_Ψ₂Sq ..
  refine (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed F (AlgebraicClosure F) _ _).mpr ?_
  intro a
  rcases eq_or_ne (aeval a (W.preΨ (n : ℤ))) 0 with h | h
  · refine Or.inr ?_
    have hk := (disjoint_and_separable_preΨ_of_even_of_isAlgClosed
      (W := W⁄(AlgebraicClosure F)) h2' heven hn').1 a
      (by rw [hmapp, eval_map, ← aeval_def]; exact h)
    rw [hmapq, eval_map, ← aeval_def] at hk
    exact hk
  · exact Or.inl h

/-- **`preΨₙ` is separable at even `n`**, for an elliptic curve over any field with `(2 : F) ≠ 0`
and `(n : F) ≠ 0`.

⚠️ **The even-`n` counterpart of `EllipticCurves.Torsion.OddTorsionCountSplits`'
`separable_preΨ_of_odd`, reached by a different route.**  That one descends along
`card_torsion_eq_sq_iff_separable_preΨ`, whose `Odd n` binder is what makes it odd-only; this one
descends along the counting bound of the core lemma and needs no iff at all.  ⚠️ **So the
`#E[n] = n² ↔ Separable (preΨ n)` bridge that `#2307` identifies as the second missing ingredient
is still `Odd`-gated, and this file does not widen it.**  Only `Polynomial.separable_map` is shared
between the two proofs. -/
theorem separable_preΨ_of_even [W.IsElliptic] (h2 : (2 : F) ≠ 0) {n : ℕ} (heven : Even n)
    (hn : (n : F) ≠ 0) : (W.preΨ (n : ℤ)).Separable := by
  classical
  haveI : (W⁄(AlgebraicClosure F)).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F (AlgebraicClosure F))).IsElliptic
  have h2' : (2 : AlgebraicClosure F) ≠ 0 := by
    simpa using algebraMap_natCast_ne_zero' (L := AlgebraicClosure F) (n := 2) (by simpa using h2)
  have hn' : ((n : ℕ) : AlgebraicClosure F) ≠ 0 := algebraMap_natCast_ne_zero' hn
  have hsep := (disjoint_and_separable_preΨ_of_even_of_isAlgClosed
    (W := W⁄(AlgebraicClosure F)) h2' heven hn').2
  rw [show (W⁄(AlgebraicClosure F)).preΨ (n : ℤ)
      = (W.preΨ (n : ℤ)).map (algebraMap F (AlgebraicClosure F)) from map_preΨ ..] at hsep
  exact (Polynomial.separable_map _).mp hsep

/-- **`preΨₙ` is separable at EVERY `n`**, for an elliptic curve over any field with `(2 : F) ≠ 0`
and `(n : F) ≠ 0` — the general-`n` member, with no parity hypothesis.

⚠️ **This is the statement `#2307` wanted and could not find**: its pricing comment enumerates the
tree's six `Separable (preΨ …)` members and records that every one is `Odd`-gated or at a fixed odd
index.  It is the two parities joined, not a new argument, and the even half is where the content
is. -/
theorem separable_preΨ [W.IsElliptic] (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : (n : F) ≠ 0) :
    (W.preΨ (n : ℤ)).Separable := by
  rcases Nat.even_or_odd n with he | ho
  · exact separable_preΨ_of_even h2 he hn
  · exact separable_preΨ_of_odd h2 ho hn

/-! ### The fibre over a root of `Ψ₂Sq` is a singleton -/

/-- **Exactly one point of `W` lies above a root of `Ψ₂Sq`**, over any field with `(2 : F) ≠ 0`:
`Ψ₂Sq.eval x = (2y + a₁x + a₃)²` for a point `(x, y)`, so the quadratic in `y` has a repeated root
and `y = −(a₁x + a₃)/2` is the only one — and it is already in `F`, so no squareness hypothesis is
needed here.

⚠️ **This is the companion of `card_setOf_equation_eq_two_of_isSquare`
(`EllipticCurves.Torsion.ThreeTorsionStructure`) at exactly the values its `hx` excludes.**  That
one asks `W.Ψ₂Sq.eval x ≠ 0` to keep the two square roots apart; here they coincide and the count
drops to one.  Together the two cover the even-`n` support with no gap and no overlap. -/
lemma card_setOf_equation_eq_one_of_eval_Ψ₂Sq_eq_zero (h2 : (2 : F) ≠ 0) {x : F}
    (hx : W.Ψ₂Sq.eval x = 0) : Nat.card {y : F // W.Equation x y} = 1 := by
  have hy : ∀ y : F, W.Equation x y → 2 * y + W.a₁ * x + W.a₃ = 0 := fun y h =>
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by rw [← Ψ₂Sq_eval_eq_sq h, hx])
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun y₁ y₂ => Subtype.ext ?_⟩, ⟨⟨W.twoTorsionY x, equation_twoTorsionY h2 hx⟩⟩⟩
  have hd : 2 * (y₁.1 - y₂.1) = 0 := by linear_combination hy _ y₁.2 - hy _ y₂.2
  exact sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left h2)

/-! ### The even-index factorisation of `ΨSqₙ`, and membership from it -/

/-- `ΨSqₙ(x) = preΨₙ(x)² · Ψ₂Sq(x)` at even `n` — Mathlib's definition with the `if` resolved. -/
private lemma eval_ΨSq_of_even {n : ℕ} (heven : Even n) (x : F) :
    (W.ΨSq (n : ℤ)).eval x = (W.preΨ (n : ℤ)).eval x ^ 2 * W.Ψ₂Sq.eval x := by
  rw [show W.ΨSq (n : ℤ) = W.preΨ (n : ℤ) ^ 2 * (if Even ((n : ℤ)) then W.Ψ₂Sq else 1) from rfl,
    if_pos (by exact_mod_cast heven : Even ((n : ℤ))), eval_mul, eval_pow]

/-- A point whose `x`-coordinate is a root of `ΨSqₙ` is `n`-torsion, with `(2 : F) ≠ 0`, for an
elliptic curve: `ψₙ(x, y)² = ΨSqₙ(x) = 0`, and `ψₙ(x, y) = 0` is `n • P = 0` by
`nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic`.

⚠️ **This is the step that lets BOTH branches of the even description share one proof**, which is
why the file does not route the `Ψ₂Sq` branch through `W.torsion 2 ≤ W.torsion n`: at even `n` a
root of `Ψ₂Sq` is a root of `ΨSqₙ` by the factorisation above, and nothing about `2 ∣ n` is needed
beyond that. -/
private lemma mem_torsion_of_eval_ΨSq_eq_zero [DecidableEq F] [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    {n : ℕ} {x y : F} (hns : W.Nonsingular x y) (hx : (W.ΨSq (n : ℤ)).eval x = 0) :
    (Point.some x y hns : W.Point) ∈ W.torsion n :=
  mem_torsion_iff.mpr ((nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic h2 hns n).mpr
    (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by rw [ψ_sq_evalEval hns.left, hx])))

/-! ### The root count and the bijection -/

section Count

variable [DecidableEq F] [W.IsElliptic]

omit [DecidableEq F] in
/-- **`preΨₙ` has exactly `(n² − 4)/2` roots** at even `n`, for an elliptic curve over any field
with `(2 : F) ≠ 0` and `(n : F) ≠ 0` over which it **splits**.

Its degree is `(n² − 4)/2` there — `WeierstrassCurve.natDegree_preΨ` on the **even** branch of its
own `if` — and `separable_preΨ_of_even` rules out a repeated one, so the splitting hypothesis is the
only input that is not already a theorem.  The odd-`n` analogue is
`EllipticCurves.Torsion.OddTorsionCountSplits`' `card_roots_preΨ_of_splits`.

⚠️ `[DecidableEq F]` is omitted rather than suppressed, and `linter.unusedDecidableInType` is right
that it never reached the type: the statement is about a **polynomial** and not about `W.torsion n`,
whose own type carries the instance through `Point.instAddCommGroup`.  That is `#2308`'s fact (a),
and this is the third site in this file where the linter fires. -/
theorem card_roots_preΨ_of_splits_of_even (h2 : (2 : F) ≠ 0) {n : ℕ} (heven : Even n)
    (hn : (n : F) ≠ 0) (hsplits : (W.preΨ (n : ℤ)).Splits) :
    Nat.card {x : F // (W.preΨ (n : ℤ)).eval x = 0} = (n ^ 2 - 4) / 2 := by
  classical
  have hn' : ((n : ℤ) : F) ≠ 0 := by exact_mod_cast hn
  have hp : W.preΨ (n : ℤ) ≠ 0 := W.preΨ_ne_zero hn'
  have hdeg : (W.preΨ (n : ℤ)).natDegree = (n ^ 2 - 4) / 2 := by
    rw [W.natDegree_preΨ hn', if_pos (by exact_mod_cast heven : Even ((n : ℤ)))]
    simp
  rw [card_root_subtype hp, Multiset.toFinset_card_of_nodup
      ((nodup_roots_iff_of_splits hp hsplits).mpr (separable_preΨ_of_even h2 heven hn)), ← hdeg]
  exact splits_iff_card_roots.mp hsplits

variable (W) in
/-- The index of the even-`n` description of `E[n] \ {O}`: a point above a root of `preΨₙ`, or a
point above a root of `Ψ₂Sq`.

⚠️ A **sum** of two sigmas rather than one sigma over a union, and that is the design decision the
disjointness pays for: as a sum it is an index only because no `x` is in both halves, and the
two halves then carry different fibre counts (`2` and `1`) with no case split inside the sum. -/
abbrev evenIndex (n : ℕ) :=
  ((x : {x : F // (W.preΨ (n : ℤ)).eval x = 0}) × {y : F // W.Equation x.1 y}) ⊕
    ((x : {x : F // W.Ψ₂Sq.eval x = 0}) × {y : F // W.Equation x.1 y})

/-- The `n`-torsion point attached to a member of `evenIndex`, with `none` sent to the point at
infinity.  Both branches discharge membership through `mem_torsion_of_eval_ΨSq_eq_zero`. -/
def torsionEvenOfPair (h2 : (2 : F) ≠ 0) {n : ℕ} (heven : Even n) :
    Option (evenIndex W n) → W.torsion n
  | none => 0
  | some (.inl ⟨x, y⟩) => ⟨Point.some x.1 y.1 (equation_iff_nonsingular.mp y.2),
      mem_torsion_of_eval_ΨSq_eq_zero h2 _ (by rw [eval_ΨSq_of_even heven, x.2]; ring)⟩
  | some (.inr ⟨x, y⟩) => ⟨Point.some x.1 y.1 (equation_iff_nonsingular.mp y.2),
      mem_torsion_of_eval_ΨSq_eq_zero h2 _ (by rw [eval_ΨSq_of_even heven, x.2]; ring)⟩

/-- `torsionEvenOfPair` is a bijection.

⚠️ **Injectivity is where the disjointness is spent, and it is spent on the two CROSS cases
only** — `inl` against `inr` and `inr` against `inl`.  Within a branch a point is its coordinate
pair, exactly as at odd `n`; across branches the two `x`-coordinates are equal and
`eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero_of_even` refutes that.  ⚠️ **Without it the map is genuinely
not injective** and the count would exceed `n²`, so this is not a convenience of the proof.

Surjectivity is `mem_preΨ_union_Ψ₂Sq_of_mem_torsion` (`EllipticCurves.Torsion.XSupport`), which is
stated at every `n` rather than only at even `n` and so needs no parity work here. -/
lemma torsionEvenOfPair_bijective (h2 : (2 : F) ≠ 0) {n : ℕ} (heven : Even n) (hn : (n : F) ≠ 0) :
    Function.Bijective (torsionEvenOfPair (W := W) h2 heven) := by
  constructor
  · rintro (_ | (⟨⟨x₁, hx₁⟩, ⟨y₁, hy₁⟩⟩ | ⟨⟨x₁, hx₁⟩, ⟨y₁, hy₁⟩⟩))
      (_ | (⟨⟨x₂, hx₂⟩, ⟨y₂, hy₂⟩⟩ | ⟨⟨x₂, hx₂⟩, ⟨y₂, hy₂⟩⟩)) hab <;>
      first
        | rfl
        | exact absurd (congrArg Subtype.val hab).symm (Point.some_ne_zero _)
        | exact absurd (congrArg Subtype.val hab) (Point.some_ne_zero _)
        | (have hxy := congrArg Subtype.val hab
           rw [torsionEvenOfPair, torsionEvenOfPair, Point.some.injEq] at hxy
           obtain ⟨rfl, rfl⟩ := hxy
           first
             | rfl
             | exact absurd hx₂ (eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero_of_even h2 heven hn hx₁)
             | exact absurd hx₁ (eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero_of_even h2 heven hn hx₂))
  · rintro ⟨(_ | ⟨x, y, h⟩), hP⟩
    · exact ⟨none, rfl⟩
    · rcases mem_preΨ_union_Ψ₂Sq_of_mem_torsion h2 hP with hx | hx
      · exact ⟨some (.inl ⟨⟨x, hx⟩, ⟨y, h.1⟩⟩), rfl⟩
      · exact ⟨some (.inr ⟨⟨x, hx⟩, ⟨y, h.1⟩⟩), rfl⟩

/-- **At even `n`, `E[n]` is the point at infinity, the points above the roots of `preΨₙ`, and the
points above the roots of `Ψ₂Sq`** — with `(2 : F) ≠ 0` and `(n : F) ≠ 0`, for an elliptic curve
over any field. -/
noncomputable def torsionEvenPairEquiv (h2 : (2 : F) ≠ 0) {n : ℕ} (heven : Even n)
    (hn : (n : F) ≠ 0) : W.torsion n ≃ Option (evenIndex W n) :=
  (Equiv.ofBijective _ (torsionEvenOfPair_bijective (W := W) h2 heven hn)).symm

/-! ### The count -/

/-- **`#E[n] = 2 · #{roots of preΨₙ} + #{roots of Ψ₂Sq} + 1`** at even `n`, for an elliptic curve
over any field with `(2 : F) ≠ 0` and `(n : F) ≠ 0` over which `Ψ₂Sq` is a **square at every root
of `preΨₙ`**.

⚠️ **The relation rather than the value**, on the precedent `#2300` and `#2302` set for figures, and
`EllipticCurves.Torsion.OddTorsionCountSplits`' `card_torsion_odd_of_isSquare` is the odd-`n` one.
⚠️ **The second term is the whole difference between the parities**: at odd `n` it is absent, and at
`n = 2` it is the only term there is.

The squareness hypothesis is spent on the `preΨₙ` branch alone — the other half of
`card_setOf_equation_eq_two_of_isSquare`'s pair is free by
`eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero_of_even` — and the `Ψ₂Sq` branch needs no hypothesis at all
by `card_setOf_equation_eq_one_of_eval_Ψ₂Sq_eq_zero`. -/
theorem card_torsion_even_of_isSquare (h2 : (2 : F) ≠ 0) {n : ℕ} (heven : Even n)
    (hn : (n : F) ≠ 0)
    (hsq : ∀ x : F, (W.preΨ (n : ℤ)).eval x = 0 → IsSquare (W.Ψ₂Sq.eval x)) :
    Nat.card (W.torsion n) = 2 * Nat.card {x : F // (W.preΨ (n : ℤ)).eval x = 0}
      + Nat.card {x : F // W.Ψ₂Sq.eval x = 0} + 1 := by
  have hn' : ((n : ℤ) : F) ≠ 0 := by exact_mod_cast hn
  have hp : W.preΨ (n : ℤ) ≠ 0 := W.preΨ_ne_zero hn'
  have hq : W.Ψ₂Sq ≠ 0 := W.Ψ₂Sq_ne_zero (four_ne_zero' h2)
  haveI : Finite {x : F // (W.preΨ (n : ℤ)).eval x = 0} :=
    Set.Finite.to_subtype (finite_setOf_isRoot hp)
  haveI : Fintype {x : F // (W.preΨ (n : ℤ)).eval x = 0} := Fintype.ofFinite _
  haveI : Finite {x : F // W.Ψ₂Sq.eval x = 0} := Set.Finite.to_subtype (finite_setOf_isRoot hq)
  haveI : Fintype {x : F // W.Ψ₂Sq.eval x = 0} := Fintype.ofFinite _
  haveI : ∀ x : F, Finite {y : F // W.Equation x y} :=
    fun x => (W.setOf_equation_finite x).to_subtype
  have hfibA : ∀ x : {x : F // (W.preΨ (n : ℤ)).eval x = 0},
      Nat.card {y : F // W.Equation x.1 y} = 2 :=
    fun x => card_setOf_equation_eq_two_of_isSquare h2
      (eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero_of_even h2 heven hn x.2) (hsq x.1 x.2)
  have hfibB : ∀ x : {x : F // W.Ψ₂Sq.eval x = 0},
      Nat.card {y : F // W.Equation x.1 y} = 1 :=
    fun x => card_setOf_equation_eq_one_of_eval_Ψ₂Sq_eq_zero h2 x.2
  rw [Nat.card_congr (torsionEvenPairEquiv h2 heven hn), Finite.card_option, Nat.card_sum,
    Nat.card_sigma, Nat.card_sigma, Finset.sum_congr rfl fun x _ => hfibA x,
    Finset.sum_congr rfl fun x _ => hfibB x, Finset.sum_const, Finset.sum_const,
    Finset.card_univ, Finset.card_univ, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  ring

/-- **`#E[n] = n²`** for an elliptic curve over **any** field with `(2 : F) ≠ 0` and `(n : F) ≠ 0`,
at **even** `n`, over which `preΨₙ` **splits**, `Ψ₂Sq` **splits**, and `Ψ₂Sq` is a **square at
every root of `preΨₙ`**: the point at infinity, the two points above each of the `(n² − 4)/2` roots
of `preΨₙ`, and the one point above each of the three roots of `Ψ₂Sq`.

⚠️ **The even-`n` member of the closure-free `*_of_splits` family**, whose members were
`card_torsion_two_of_splits`, `card_torsion_three_of_splits` and
`EllipticCurves.Torsion.OddTorsionCountSplits`' odd-`n` `card_torsion_eq_sq_of_splits`.

⚠️ **One hypothesis more than the odd form, and it is `W.Ψ₂Sq.Splits` rather than anything about
disjointness**: `#{roots of Ψ₂Sq} = 3` is a term of this relation and not of the odd one, so it has
to be pinned.  The disjointness and the separability that a reader might expect beside it are
theorems of this file. -/
theorem card_torsion_eq_sq_of_splits_of_even (h2 : (2 : F) ≠ 0) {n : ℕ} (heven : Even n)
    (hn : (n : F) ≠ 0) (hsplits : (W.preΨ (n : ℤ)).Splits) (hsplits₂ : W.Ψ₂Sq.Splits)
    (hsq : ∀ x : F, (W.preΨ (n : ℤ)).eval x = 0 → IsSquare (W.Ψ₂Sq.eval x)) :
    Nat.card (W.torsion n) = n ^ 2 := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  rw [card_torsion_even_of_isSquare h2 heven hn hsq,
    card_roots_preΨ_of_splits_of_even h2 heven hn hsplits, card_roots_Ψ₂Sq_of_splits h2 hsplits₂]
  exact two_mul_sq_sub_four_div_two_add_four heven hn0

/-- **`#E[n] = n²` at EVERY `n`** for an elliptic curve over any field with `(2 : F) ≠ 0` and
`(n : F) ≠ 0` over which `preΨₙ` **splits**, `Ψ₂Sq` **splits**, and `Ψ₂Sq` is a **square at every
root of `preΨₙ`** — **no algebraic closure and no parity hypothesis.**

⚠️ **This is the general-`n` member of the closure-free family and the thing `#2296`'s ladder wants
as its `hcard`**, which needs `#E[n] = n²` over a finite Galois extension at every `n` with
`((n : ℤ) : F) ≠ 0` and not only at the odd ones.

⚠️ **`W.Ψ₂Sq.Splits` is not used on the odd branch**, and a caller who knows `n` is odd should take
`EllipticCurves.Torsion.OddTorsionCountSplits`' `card_torsion_eq_sq_of_splits` instead and not pay
for it.  The hypothesis is here because it is a term of the even relation; the two parities are
joined by `Nat.even_or_odd` and nothing else. -/
theorem card_torsion_eq_sq_of_splits_of_splits_Ψ₂Sq (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : (n : F) ≠ 0)
    (hsplits : (W.preΨ (n : ℤ)).Splits) (hsplits₂ : W.Ψ₂Sq.Splits)
    (hsq : ∀ x : F, (W.preΨ (n : ℤ)).eval x = 0 → IsSquare (W.Ψ₂Sq.eval x)) :
    Nat.card (W.torsion n) = n ^ 2 := by
  rcases Nat.even_or_odd n with he | ho
  · exact card_torsion_eq_sq_of_splits_of_even h2 he hn hsplits hsplits₂ hsq
  · exact card_torsion_eq_sq_of_splits h2 ho hn hsplits hsq

/-! ### Recovery of the landed `n = 2` member -/

/-- **`card_torsion_two_of_splits` is this file's theorem at `n = 2`**, hypothesis for hypothesis.

⚠️ **This is the recovery `EllipticCurves.Torsion.OddTorsionCountSplits` records as impossible from
the odd form**, and it goes through here because `preΨ₂ = 1` makes both of the `preΨ`-side
hypotheses free — a unit splits, and it has no roots, so the squareness condition is vacuous — and
leaves `W.Ψ₂Sq.Splits` as the only surviving hypothesis, which is `card_torsion_two_of_splits`'
only hypothesis.

⚠️ The statement is quoted rather than referenced so that a drift in either direction fails here:
the hypothesis, the characteristic condition and the value `4` are all written out. -/
example (h2 : (2 : F) ≠ 0) (hsplits : W.Ψ₂Sq.Splits) : Nat.card (W.torsion 2) = 4 := by
  have h : W.preΨ ((2 : ℕ) : ℤ) = 1 := by
    rw [show (((2 : ℕ) : ℤ)) = (2 : ℤ) from rfl]
    simp [WeierstrassCurve.preΨ]
  have hcard := card_torsion_eq_sq_of_splits_of_even (W := W) (n := 2) h2 (by decide)
    (by exact_mod_cast h2) (by rw [h]; exact Splits.one) hsplits
    (fun x hx => by rw [h] at hx; simp at hx)
  simpa using hcard

end Count

/-! ### Non-vacuity over a field that is not algebraically closed

The certificate curve is the shared `EllipticCurves.Fixture.y2EqX3Add5X2Add4X` at `R = ℚ`:
`y² = x³ + 5x² + 4x = x(x + 1)(x + 4)`, whose `2`-torsion cubic has the three distinct rational
roots `0`, `−1`, `−4`.  ⚠️ **What this block tests is that the even form of this file is not vacuous
over a field with no algebraic closure in sight** — every hypothesis is discharged over `ℚ` itself.

⚠️ **It certifies ONE even index and the module docstring says why it is the only cheap one**: at
`n = 4` the even headline additionally needs `(W.preΨ 4).Splits`, and full rational `4`-torsion
forces `4 ∣ #μ(ℚ) = 2`.  A finite base is needed there, and the obstruction argument is classical
and formalised nowhere in this tree. -/

section Nonvacuity

open EllipticCurves.Fixture

/-- The `2`-torsion cubic of the certificate curve, factored: `4X³ + 20X² + 16X`.  ⚠️ A copy of
`EllipticCurves.Torsion.TwoTorsion`'s `Ψ₂Sq_y2EqX3Add5X2Add4X`, which is `private` there; see the
module docstring on the three replicated helpers. -/
private lemma Ψ₂Sq_fixture :
    (y2EqX3Add5X2Add4X ℚ).Ψ₂Sq = C 4 * X * (X + C 1) * (X + C 4) := by
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, y2EqX3Add5X2Add4X]
  norm_num only
  simp only [map_ofNat, map_one, Polynomial.C_0]
  ring

/-- **The splitting hypothesis, discharged over `ℚ`** — a constant times three monic linear factors
is a `Splits` witness on the nose. -/
private lemma splits_Ψ₂Sq_fixture : (y2EqX3Add5X2Add4X ℚ).Ψ₂Sq.Splits := by
  rw [Ψ₂Sq_fixture]
  exact (((Splits.C 4).mul Splits.X).mul (Splits.X_add_C 1)).mul (Splits.X_add_C 4)

/-- **`#E[2] = 4` over `ℚ` with no hypothesis whatsoever, FROM THE EVEN FORM OF THIS FILE**, for
`y² = x(x + 1)(x + 4)`.

⚠️ **`EllipticCurves.Torsion.TwoTorsion` already proves this figure on this curve from
`card_torsion_two_of_splits`.** What is new is the route: this is
`card_torsion_eq_sq_of_splits_of_even` at `n = 2`, so the even-`n` relation, the singleton fibre
over a root of `Ψ₂Sq`, and the `(n² − 4)/2 = 0` degree branch are all exercised on a concrete curve
over a field that is not algebraically closed.  **A count that agrees with a landed one by a
different route is the cheapest check this file can carry.** -/
private theorem card_torsion_two_fixture :
    Nat.card ((y2EqX3Add5X2Add4X ℚ).torsion 2) = 4 := by
  have h : (y2EqX3Add5X2Add4X ℚ).preΨ ((2 : ℕ) : ℤ) = 1 := by
    rw [show (((2 : ℕ) : ℤ)) = (2 : ℤ) from rfl]
    simp [WeierstrassCurve.preΨ]
  have hcard := card_torsion_eq_sq_of_splits_of_even (W := y2EqX3Add5X2Add4X ℚ) (n := 2)
    (by norm_num) (by decide) (by norm_num) (by rw [h]; exact Splits.one) splits_Ψ₂Sq_fixture
    (fun x hx => by rw [h] at hx; simp at hx)
  simpa using hcard

end Nonvacuity

end WeierstrassCurve.Affine
