/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.OddTorsionCount
import EllipticCurves.Torsion.OmegaChordSum

/-!
# `#E[n] = n²` at odd `n` over a field that is not algebraically closed

Every general-`n` and every odd-`n` counting statement in this development binds
`[IsAlgClosed F]`: `EllipticCurves.Torsion.StructureGeneral`'s `card_torsion_eq_sq`,
`EllipticCurves.Torsion.OmegaChordSum`'s `card_torsion_eq_sq_of_odd`, and the five further
members `#2305` enumerates.  ⚠️ **A statement that binds a closure cannot supply
`Nat.card ((W⁄N).torsion n) = n ^ 2` over a FINITE Galois extension `N / F`, which is the only
place `#2296`'s ladder wants it.**  The closure-free family that the two landed towers actually
consume is `card_torsion_two_of_splits` (`EllipticCurves.Torsion.TwoTorsion`) and
`card_torsion_three_of_splits` (`EllipticCurves.Torsion.ThreeTorsionStructure`), and it had no
general-`n` member.  This file is that member, at odd `n`.

## The two hypotheses, and what the closure was doing

`card_torsion_eq_sq_of_splits` asks, beside `(2 : F) ≠ 0` and `(n : F) ≠ 0` and `Odd n`:

```
hsplits : (W.preΨ n).Splits
hsq     : ∀ x, (W.preΨ n).eval x = 0 → IsSquare (W.Ψ₂Sq.eval x)
```

which is `card_torsion_three_of_splits`' pair with `Ψ₃` replaced by `preΨₙ`, and the second has
no `n = 2` counterpart for the reason that file records: the description of `E[n]` at odd `n` is a
**sigma** over the roots of `preΨₙ`, and splitting `preΨₙ` fixes only the base of that sigma.
⚠️ **Splitting is a statement about `preΨₙ`; squareness is a statement about a different
polynomial, and no amount of splitting `preΨₙ` supplies it.**

⚠️ **The closure of `EllipticCurves.Torsion.OddTorsionCount` was doing exactly one thing, in two
places, and the places are the measurement rather than the reading of a docstring**: producing a
`y` above an `x` by `exists_equation'`, once inside `fibreY` / `equation_fibreY` and once inside
`eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero`.  Both are replaced here by
`exists_equation_of_isSquare`, which is the same completion of the same quadratic with the square
root supplied instead of assumed.

⚠️⚠️ **And one of the two uses is FREE, which is why this file asks for squareness at the roots of
`preΨₙ` and not everywhere**: the non-degeneracy lemma argues from `W.Ψ₂Sq.eval x = 0`, and `0` is
a square in every ring.  So `eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero'` below costs `(2 : F) ≠ 0`
and nothing else.  ⚠️ **It does not supersede the landed lemma and must not be read as doing so**:
that one holds **in every characteristic** — `#2253` spent a round removing its `(2 : F) ≠ 0` —
and this one does not.  The two are incomparable, and the primed name is the tree's marker for
that rather than for a successor.

## The relation, not only the numeral

The count this file reaches is an equality between a curve and a polynomial, and it is stated
separately from the value it takes when the polynomial splits:

```
#E[n] = 2 · #{roots of preΨₙ} + 1                                 (odd n, h2, (n : F) ≠ 0, hsq)
      = 2 · (n² − 1)/2 + 1 = n²                                   (and preΨₙ splits)
```

⚠️ **Separability is not a hypothesis of either step, and that is a theorem of this file rather
than an omission**: `separable_preΨ_of_odd` proves `Separable (W.preΨ n)` over **any** field with
`(2 : F) ≠ 0` and `(n : F) ≠ 0` at odd `n`, by base change to `AlgebraicClosure F` and
`Polynomial.separable_map`.  ⚠️ So the only live input to the root count is the **splitting**
hypothesis, and `(n² − 1)/2` is not a separate assumption about multiplicities.

## ⚠️ `omit [IsAlgClosed F] in` is a SILENT NO-OP on a `def`, and `#2305` prescribes it as the test

`#2305`'s acceptance asks whether `torsionOddEquiv`'s `[IsAlgClosed F]` is load-bearing, *"with
the measurement (`omit` it and build)"*.  ⚠️ **Run on `torsionOddEquiv` that measurement returns a
FALSE GREEN.**  Measured at `22db66e`:

* `omit [IsAlgClosed F] in` before `torsionOddEquiv`, a `noncomputable def` — the file compiles
  with **no error and no warning**, and `#check @torsionOddEquiv` still reports `[IsAlgClosed F]`,
  re-added as an **anonymous** instance binder.  The binder is not removed; only the name is.
* the same edit before `torsionOddOfRoot_bijective`, a `lemma` — the build fails, with
  `error: cannot omit referenced section variable 'inst✝¹'`.
  ⚠️ **This is the sound half of the test and it says the closure IS load-bearing.**
* a two-declaration control outside this development reproduces the split exactly: `omit` before a
  `def` whose body calls `IsAlgClosed.exists_pow_nat_eq` compiles and keeps the binder; `omit`
  before a `theorem` whose proof does the same fails to synthesize.

⚠️ **So the answer to `#2305`'s question is YES, load-bearing — and the instrument it names
cannot establish that on a `def`.** `#check` on the elaborated signature is the test that can, and
it is the one `#2266` already prescribes for binder claims.

## ⚠️ What is NOT here: even `n`, and `n = 2` is not an instance of anything below

`#2305` allows either coverage of both parities or odd `n` with the even case filed, and this is
the second.  The even-`n` count is **not** this statement with `Odd n` deleted:

* the relation gains a term — at even `n` the roots of `Ψ₂Sq` *are* roots of `ΨSqₙ`, their fibres
  are singletons, and the count is `2 · #{roots of preΨₙ} + #{roots of Ψ₂Sq} + 1`;
* that arithmetic reaches `n²` only if the two root sets are **disjoint**, i.e. only from
  `IsCoprime (W.preΨ n) W.Ψ₂Sq` at even `n`.  ⚠️ **The tree does not have it.**
  `IsCoprime W.Ψ₃ W.Ψ₂Sq` is merged (`EllipticCurves.Torsion.TwoThreeDisjoint`) and `3` is odd;
  the odd-`n` form of the same fact is `eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero`, which spends
  oddness in terms.
* ⚠️⚠️ **`card_torsion_two_of_splits` is therefore not recoverable from any form below, and the
  reason is a degeneracy and not the parity**: `W.preΨ 2 = 1` (machine-checked below), so at
  `n = 2` the hypotheses of the general form are *vacuously true* — a unit splits and has no roots
  — while `#E[2] = 4` is false over `ℚ` for `y² = x³ − 2`.  The `n = 2` member's splitting
  hypothesis is on `Ψ₂Sq`, which is the term the even-`n` relation adds, and at `n = 2` it is the
  **only** term.  **So the even-`n` row subsumes it and the odd-`n` row cannot.**

## ⚠️ Non-vacuity, and what is not certified

`EllipticCurves.Torsion.ThreeTorsionSplitCertificate` discharges both hypotheses of
`card_torsion_three_of_splits` on `y² = x³ + 2` over `ZMod 7`, so the pair below is jointly
satisfiable over a field that is not algebraically closed at `n = 3`, and the recovery `example`
is the machine-checked half of that.  ⚠️ **No certificate is shipped at `n ≥ 5` and the gap is
real**: over `ℚ` the two hypotheses together say `E[n] ⊆ E(F)`, which forces `μₙ ⊆ F` through the
Weil pairing and is unsatisfiable for every `n ≥ 3`, so a certificate needs a finite base and a
degree-`(n² − 1)/2` polynomial split over it.  That argument is classical, is **not formalised
anywhere in this tree** — `#244` is the Weil-pairing front — and nothing in this file rests on it;
it is recorded because it is also why `#2296`'s tower is not a convenience.

## Main statements

* `WeierstrassCurve.Affine.separable_preΨ_of_odd` : `Separable (W.preΨ n)` at odd `n` with
  `(2 : F) ≠ 0` and `(n : F) ≠ 0`, for an elliptic curve over **any** field.
* `WeierstrassCurve.Affine.eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero'` : at odd `n` with
  `(2 : F) ≠ 0`, a root of `preΨₙ` is not a root of `Ψ₂Sq`, for an elliptic curve.
* `WeierstrassCurve.Affine.card_roots_preΨ_of_splits` : `#{roots of preΨₙ} = (n² − 1)/2`.
* `WeierstrassCurve.Affine.torsionOddPairEquiv` : `E[n] ≃ Option (Σ x, {y // Equation x y})`.
* `WeierstrassCurve.Affine.card_torsion_odd_of_isSquare` : the relation
  `#E[n] = 2 · #{roots of preΨₙ} + 1`.
* **`WeierstrassCurve.Affine.card_torsion_eq_sq_of_splits`** : `#E[n] = n²` at odd `n` with
  `(2 : F) ≠ 0` and `(n : F) ≠ 0`, for an elliptic curve over a field over which `preΨₙ` splits
  and `Ψ₂Sq` is a square at every root of it — **no algebraic closure**.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6, Corollary 6.4.
-/

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-! ### Separability of `preΨₙ` with no closure -/

private lemma algebraMap_natCast_ne_zero {L : Type*} [Field L] [Algebra F L] {n : ℕ}
    (h : (n : F) ≠ 0) : (n : L) ≠ 0 := by
  rw [← map_natCast (algebraMap F L) n, ne_eq, map_eq_zero]
  exact h

/-- **`preΨₙ` is separable at odd `n`, for an elliptic curve over any field with `(2 : F) ≠ 0`
and `(n : F) ≠ 0`.**

`EllipticCurves.Torsion.OmegaChordSum`'s `card_torsion_eq_sq_of_odd` and
`EllipticCurves.Torsion.OddTorsionCount`'s `card_torsion_eq_sq_iff_separable_preΨ` give this over
`AlgebraicClosure F`, and `Polynomial.separable_map` brings it back down: separability of a
polynomial over a field is unchanged by a field extension, so the closure is spent on the proof
and not on the statement.

⚠️ **This is why no form below takes separability as a hypothesis.**  The pattern is
`EllipticCurves.Torsion.ThreeDivisionField`'s `separable_Ψ₃` one index down, which does the same
descent through a splitting field rather than a closure; this one needs a closure because
`card_torsion_eq_sq_of_odd` is where the general-`n` separability lives. -/
theorem separable_preΨ_of_odd [W.IsElliptic] (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n)
    (hn : (n : F) ≠ 0) : (W.preΨ (n : ℤ)).Separable := by
  classical
  haveI : (W⁄(AlgebraicClosure F)).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F (AlgebraicClosure F))).IsElliptic
  have h2' : (2 : AlgebraicClosure F) ≠ 0 := by
    simpa using algebraMap_natCast_ne_zero (L := AlgebraicClosure F) (n := 2) (by simpa using h2)
  have hn' : ((n : ℕ) : AlgebraicClosure F) ≠ 0 := algebraMap_natCast_ne_zero hn
  have hsep := (card_torsion_eq_sq_iff_separable_preΨ (W := W⁄(AlgebraicClosure F))
    h2' hodd hn').mp (card_torsion_eq_sq_of_odd h2' hodd hn')
  rw [show (W⁄(AlgebraicClosure F)).preΨ (n : ℤ)
      = (W.preΨ (n : ℤ)).map (algebraMap F (AlgebraicClosure F)) from map_preΨ ..] at hsep
  exact (Polynomial.separable_map _).mp hsep

/-! ### A root of `preΨₙ` is not a root of `Ψ₂Sq`, with no closure -/

/-- **At an odd index, a root of `preΨₙ` is not a root of `Ψ₂Sq`**, for an elliptic curve over any
field with `(2 : F) ≠ 0`.

The proof of `eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero` with its one closure use replaced: a common
root carries a point `(x, y)` of `W`, and here that point comes from
`exists_equation_of_isSquare` rather than from `exists_equation'`, because the hypothesis under
refutation is `W.Ψ₂Sq.eval x = 0` and ⚠️ **`0` is a square in every ring, so the squareness this
file asks for elsewhere is free at exactly the values where it would be needed.**  The rest is
unchanged: such a point is `2`-torsion, and `ψ` does not vanish at an odd index at a `2`-torsion
point.

⚠️ **This does NOT supersede the unprimed lemma and the two are incomparable.** That one binds
`[IsAlgClosed F]` and holds **in every characteristic**, which `#2253` established by removing its
`(2 : F) ≠ 0`; this one drops the closure and buys the hypothesis back.  A caller over `F̄` in
characteristic `2` has only the unprimed form, and a caller over a finite extension has only this
one. -/
theorem eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero' [W.IsElliptic] (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : Odd n) {x : F} (hx : (W.preΨ (n : ℤ)).eval x = 0) : W.Ψ₂Sq.eval x ≠ 0 := by
  intro hΨ₂
  obtain ⟨y, hxy⟩ := exists_equation_of_isSquare h2 (x := x) ⟨0, by rw [hΨ₂]; ring⟩
  have ht : (W.ψ 2).evalEval x y = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by rw [ψ_sq_evalEval hxy 2, ΨSq_two, hΨ₂])
  have hψn : (W.ψ (n : ℤ)).evalEval x y = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by
      rw [ψ_sq_evalEval hxy, ΨSq_natCast_eq_sq_of_odd hn, eval_pow, hx,
        zero_pow (two_ne_zero (α := ℕ))])
  obtain ⟨m, hm⟩ := hn
  refine ψ_odd_evalEval_ne_zero_of_ψ_two_evalEval_eq_zero ht
    (ψ_three_evalEval_ne_zero_of_ψ_two_evalEval_eq_zero hxy ht) m ?_
  rw [show 2 * (m : ℤ) + 1 = ((n : ℕ) : ℤ) by rw [hm]; push_cast; ring]
  exact hψn

/-! ### The root count -/

section Count

variable [DecidableEq F] [W.IsElliptic]

omit [DecidableEq F] in
/-- **`preΨₙ` has exactly `(n² − 1)/2` roots** at odd `n`, for an elliptic curve over any field
with `(2 : F) ≠ 0` and `(n : F) ≠ 0` over which it **splits**.

Its degree is `(n² − 1)/2` there (`WeierstrassCurve.natDegree_preΨ` on the odd branch) and
`separable_preΨ_of_odd` rules out a repeated one, so the splitting hypothesis is the only input
that is not already a theorem.  This is the odd-`n` analogue of `card_roots_Ψ₃_of_splits`
(`EllipticCurves.Torsion.ThreeTorsionStructure`) and of `card_roots_Ψ₂Sq_of_splits`
(`EllipticCurves.Torsion.TwoTorsion`). -/
theorem card_roots_preΨ_of_splits (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n) (hn : (n : F) ≠ 0)
    (hsplits : (W.preΨ (n : ℤ)).Splits) :
    Nat.card {x : F // (W.preΨ (n : ℤ)).eval x = 0} = (n ^ 2 - 1) / 2 := by
  classical
  have hp : W.preΨ (n : ℤ) ≠ 0 := W.preΨ_ne_zero (R := F) (by push_cast; exact hn)
  have hdeg : (W.preΨ (n : ℤ)).natDegree = (n ^ 2 - 1) / 2 := by
    rw [W.natDegree_preΨ (R := F) (by push_cast; exact hn)]
    simp [Nat.not_even_iff_odd.mpr hodd]
  rw [card_root_subtype hp, Multiset.toFinset_card_of_nodup
      ((nodup_roots_iff_of_splits hp hsplits).mpr (separable_preΨ_of_odd h2 hodd hn)), ← hdeg]
  exact splits_iff_card_roots.mp hsplits

/-! ### The bijection, as a sigma over the roots -/

/-- The `n`-torsion point attached to a root `x` of `preΨₙ` together with a `y`-coordinate above
it, with `none` sent to the point at infinity.

⚠️ A **sigma** and not a `Bool`-indexed product, unlike
`EllipticCurves.Torsion.OddTorsionCount`'s `torsionOddOfRoot`: over a field that is not
algebraically closed the fibre can be empty, so the `y` is data the map takes rather than data it
produces.  `torsionThreeOfPair` (`EllipticCurves.Torsion.ThreeTorsionStructure`) is the same
shape. -/
def torsionOddOfPair (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n) :
    Option ((x : {x : F // (W.preΨ (n : ℤ)).eval x = 0}) × {y : F // W.Equation x.1 y}) →
      W.torsion n
  | none => 0
  | some ⟨x, y⟩ => ⟨Point.some x.1 y.1 (equation_iff_nonsingular.mp y.2),
      mem_torsion_iff.mpr ((nsmul_eq_zero_iff_eval_preΨ_eq_zero h2 hodd _).mpr x.2)⟩

/-- `torsionOddOfPair` is a bijection: injective because a point is its coordinate pair, and
surjective because `nsmul_eq_zero_iff_eval_preΨ_eq_zero` puts the `x`-coordinate of every nonzero
`n`-torsion point among the roots of `preΨₙ`. -/
lemma torsionOddOfPair_bijective (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n) :
    Function.Bijective (torsionOddOfPair (W := W) h2 hodd) := by
  constructor
  · rintro (_ | ⟨⟨x₁, hx₁⟩, ⟨y₁, hy₁⟩⟩) (_ | ⟨⟨x₂, hx₂⟩, ⟨y₂, hy₂⟩⟩) hab
    · rfl
    · exact absurd (congrArg Subtype.val hab).symm (Point.some_ne_zero _)
    · exact absurd (congrArg Subtype.val hab) (Point.some_ne_zero _)
    · have hxy := congrArg Subtype.val hab
      rw [torsionOddOfPair, torsionOddOfPair, Point.some.injEq] at hxy
      obtain ⟨rfl, rfl⟩ := hxy
      rfl
  · rintro ⟨(_ | ⟨x, y, h⟩), hP⟩
    · exact ⟨none, rfl⟩
    · exact ⟨some ⟨⟨x, (nsmul_eq_zero_iff_eval_preΨ_eq_zero h2 hodd h).mp
        (mem_torsion_iff.mp hP)⟩, ⟨y, h.1⟩⟩, rfl⟩

/-- **`E[n]` is the point at infinity together with the points above the roots of `preΨₙ`**, at
odd `n` with `(2 : F) ≠ 0`, for an elliptic curve over any field. -/
noncomputable def torsionOddPairEquiv (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n) :
    W.torsion n ≃
      Option ((x : {x : F // (W.preΨ (n : ℤ)).eval x = 0}) × {y : F // W.Equation x.1 y}) :=
  (Equiv.ofBijective _ (torsionOddOfPair_bijective (W := W) h2 hodd)).symm

/-! ### The count -/

/-- **`#E[n] = 2 · #{roots of preΨₙ} + 1`** at odd `n`, for an elliptic curve over any field with
`(2 : F) ≠ 0` and `(n : F) ≠ 0` over which `Ψ₂Sq` is a **square at every root of `preΨₙ`**.

⚠️ **The relation rather than the value**, on the precedent `#2300` and `#2302` set for figures:
it names what `#E[n]` is in terms of one univariate polynomial at every odd `n`, and the `n²` of
`card_torsion_eq_sq_of_splits` is this with the root count substituted.  `card_torsion_odd`
(`EllipticCurves.Torsion.OddTorsionCount`) is the same equality over an algebraically closed
field; the squareness hypothesis here is what replaces that closure, and the other half of
`card_setOf_equation_eq_two_of_isSquare`'s pair is free by
`eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero'`. -/
theorem card_torsion_odd_of_isSquare (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n) (hn : (n : F) ≠ 0)
    (hsq : ∀ x : F, (W.preΨ (n : ℤ)).eval x = 0 → IsSquare (W.Ψ₂Sq.eval x)) :
    Nat.card (W.torsion n) = 2 * Nat.card {x : F // (W.preΨ (n : ℤ)).eval x = 0} + 1 := by
  have hp : W.preΨ (n : ℤ) ≠ 0 := W.preΨ_ne_zero (R := F) (by push_cast; exact hn)
  haveI : Finite {x : F // (W.preΨ (n : ℤ)).eval x = 0} :=
    Set.Finite.to_subtype (finite_setOf_isRoot hp)
  haveI : Fintype {x : F // (W.preΨ (n : ℤ)).eval x = 0} := Fintype.ofFinite _
  haveI : ∀ x : {x : F // (W.preΨ (n : ℤ)).eval x = 0}, Finite {y : F // W.Equation x.1 y} :=
    fun x => (W.setOf_equation_finite x.1).to_subtype
  have hfib : ∀ x : {x : F // (W.preΨ (n : ℤ)).eval x = 0},
      Nat.card {y : F // W.Equation x.1 y} = 2 :=
    fun x => card_setOf_equation_eq_two_of_isSquare h2
      (eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero' h2 hodd x.2) (hsq x.1 x.2)
  rw [Nat.card_congr (torsionOddPairEquiv h2 hodd), Finite.card_option, Nat.card_sigma,
    Finset.sum_congr rfl fun x _ => hfib x, Finset.sum_const, Finset.card_univ,
    Nat.card_eq_fintype_card]
  ring

private lemma two_mul_pred_sq_div_two_add_one {n : ℕ} (hn : Odd n) :
    2 * ((n ^ 2 - 1) / 2) + 1 = n ^ 2 := by
  obtain ⟨k, hk⟩ := hn
  have hsq : n ^ 2 = 4 * k ^ 2 + 4 * k + 1 := by subst hk; ring
  have hdiv : (n ^ 2 - 1) / 2 = 2 * k ^ 2 + 2 * k := by rw [hsq]; omega
  omega

/-- **`#E[n] = n²`** for an elliptic curve over **any** field with `(2 : F) ≠ 0` and
`(n : F) ≠ 0`, at odd `n`, over which `preΨₙ` **splits** and `Ψ₂Sq` is a **square at every root of
it**: the point at infinity together with the two points above each of the `(n² − 1)/2` roots.

⚠️ **This is the general-`n` member of the closure-free `*_of_splits` family** whose only members
were `card_torsion_two_of_splits` and `card_torsion_three_of_splits`, and it is what a counting
floor over a finite Galois extension can consume — `#2296`'s `hcard`.  The two hypotheses are
exactly `card_torsion_three_of_splits`' two, and the `n = 3` recovery below is the check that
nothing drifted.

⚠️ **Odd `n` only, and the even case is a different statement rather than this one with a binder
deleted** — see the module docstring: its relation carries a `#{roots of Ψ₂Sq}` term and needs
`IsCoprime (W.preΨ n) W.Ψ₂Sq`, which this tree does not have. -/
theorem card_torsion_eq_sq_of_splits (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n) (hn : (n : F) ≠ 0)
    (hsplits : (W.preΨ (n : ℤ)).Splits)
    (hsq : ∀ x : F, (W.preΨ (n : ℤ)).eval x = 0 → IsSquare (W.Ψ₂Sq.eval x)) :
    Nat.card (W.torsion n) = n ^ 2 := by
  rw [card_torsion_odd_of_isSquare h2 hodd hn hsq,
    card_roots_preΨ_of_splits h2 hodd hn hsplits]
  exact two_mul_pred_sq_div_two_add_one hodd

/-! ### Recovery of the landed `n = 3` member, and why `n = 2` is not one -/

/-- **`card_torsion_three_of_splits` is this file's theorem at `n = 3`**, hypothesis for
hypothesis, with `W.preΨ 3 = W.Ψ₃`.

⚠️ The statement is quoted rather than referenced so that a drift in either direction fails here:
the two hypotheses, the two characteristic conditions and the value `9` are all written out. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hsplits : W.Ψ₃.Splits)
    (hsq : ∀ x : F, W.Ψ₃.eval x = 0 → IsSquare (W.Ψ₂Sq.eval x)) :
    Nat.card (W.torsion 3) = 9 := by
  have h : W.preΨ ((3 : ℕ) : ℤ) = W.Ψ₃ := by
    rw [show (((3 : ℕ) : ℤ)) = (3 : ℤ) from rfl]
    simp [WeierstrassCurve.preΨ]
  have hcard := card_torsion_eq_sq_of_splits (W := W) (n := 3) h2 (by decide)
    (by exact_mod_cast h3) (h ▸ hsplits) fun x hx => hsq x (h ▸ hx)
  simpa using hcard

/-- ⚠️ **`W.preΨ 2 = 1`, which is why `card_torsion_two_of_splits` is not an instance of anything
above.**  At `n = 2` the hypotheses of `card_torsion_eq_sq_of_splits` are vacuous — a unit splits
and has no roots — while `#E[2] = 4` is false over a general field, so the even-`n` count has to
be carried by the `Ψ₂Sq` term and not by `preΨₙ`.  `Odd n` is therefore not a removable binder,
and this one-line `example` is the measurement that says so. -/
example : W.preΨ ((2 : ℕ) : ℤ) = 1 := by
  rw [show (((2 : ℕ) : ℤ)) = (2 : ℤ) from rfl]
  simp [WeierstrassCurve.preΨ]

end Count

end WeierstrassCurve.Affine
