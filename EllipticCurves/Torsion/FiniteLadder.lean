/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.Data.Int.Interval
import EllipticCurves.Torsion.Finite
import EllipticCurves.Torsion.NsmulLadder

/-!
# `E[n]` is finite at every index, from the division-polynomial ladder

`EllipticCurves.Torsion.Finite` is a finiteness *engine*: it turns "the nonzero `n`-torsion points
have their `x`-coordinates in a finite set `S`" into `Finite E[n]`, and it has been waiting for a
supplier of `S` since it merged.  This file supplies one.

The supplier is `WeierstrassCurve.Affine.exists_ψ_evalEval_eq_zero_of_nsmul_eq_zero`
(`EllipticCurves.Torsion.NsmulLadder`): if `n • P = 0` for a nonzero affine `P = (x, y)` then some
rung `1 ≤ k ≤ n` of the ladder vanishes, `ψ_k(x, y) = 0`.  Squaring that with `ψ_sq_evalEval` moves
it onto the `x`-axis — `ΨSq_k(x) = 0` — so

```
x(P)  ∈  ⋃ 2 ≤ k ≤ n, { roots of ΨSq_k } ,
```

a finite union of finite sets.  ⚠️ The union starts at `k = 2` because `ψ₁ = 1` is a unit, so the
`k = 1` rung can never vanish and contributes nothing.

## ⚠️ What this is not: the `n²` bound

`#252` asks for **two** things, finiteness of `E[n]` and the sharp `#E[n] ≤ n²`.  This file
delivers the first at every index and **not** the second, and the reason is structural rather than
a missing lemma.  The sharp bound needs `x(P)` in the root set of `ΨSqₙ` *alone*, of degree
`n² − 1`.  ⚠️ Even that root set does not reach `n²` along this file's route: the
two-points-per-fibre count of `card_torsion_le_of_xCoords` gives `2(n² − 1) + 1 = 2n² − 1`, and the
remaining factor of two needs a finer count than the bare root set supplies — see `#252` and the
structure theorem `#242`.  What the ladder gives is weaker still: the union of the root sets of
`ΨSq₂, …, ΨSqₙ` — equivalently the root set of their product, whose degree grows like `n³/3`.

Closing that distance is the implication `n • P = 0 → ψₙ(P) = 0` — `#251`'s scope item 2 — which is
proved neither here nor in Mathlib.  ⚠️ The route this file would have taken to it runs through the
converse `ψ_d(P) = 0 → d • P = 0` at the least vanishing index `d`, plus a way to propagate that
vanishing along `d ∣ n`; the elliptic **divisibility** half of Mathlib's standing `TODO`
(`IsDvdSequence (normEDS b c d)`) would supply the second step and is unproved there.  ⚠️ Nothing
below measures whether either step is *necessary*, and this file does not claim that it is: a
pointwise substitute for the `d ∣ n` propagation, built from Ward's relator rather than from
`IsDvdSequence`, is one of the routes `#251` records.

⚠️ So do not read `finite_torsion_of_forall_intCast_ne_zero` as closing `#252`.  It closes the
finiteness half at a general index, which the tree previously had only for `3`-smooth `n`
(`finite_torsion_of_smooth`, `EllipticCurves.Torsion.Multiplicative`, obtained from `#E[2] ≤ 4` and
`#E[3] ≤ 9` by multiplicativity and reaching no prime beyond `3`).  `E[5]` was out of reach before
this file.

## ⚠️ The characteristic hypothesis, and why it is not cosmetic

Every statement below assumes `(k : F) ≠ 0` for `2 ≤ k ≤ n`, i.e. `char F = 0` or `char F > n`.
It enters twice, and neither use is removable on this route:

* `ΨSq_ne_zero` needs `(k : F) ≠ 0` to know `ΨSq_k` is a nonzero polynomial — a *zero* polynomial
  has every element as a root and the union above would be all of `F`.  Since the ladder produces
  an unknown rung `k`, every `k ≤ n` has to be excluded, not just `k = n`.
* `(2 : F) ≠ 0` is what the ladder itself runs on, through `divY`'s halving.

⚠️ This is strictly stronger than the hypothesis the sharp bound would need (`(n : F) ≠ 0` alone),
and it is the second price of using the whole ladder rather than its top rung.  Both prices are
paid for the same reason and both would be refunded by `#251`'s scope item 2.

## Main definitions

* `WeierstrassCurve.Affine.ladderXSupport` : the finite `x`-support the ladder predicts,
  `⋃ 2 ≤ k ≤ n, {x | ΨSq_k(x) = 0}`.

## Main statements

* `WeierstrassCurve.Affine.finite_ladderXSupport` : it is finite.
* `WeierstrassCurve.Affine.mem_ladderXSupport_of_mem_torsion` : it contains the `x`-coordinate of
  every nonzero affine `n`-torsion point — the supplier `Torsion.Finite` was waiting for.
* `WeierstrassCurve.Affine.finite_torsion_of_forall_intCast_ne_zero` : **`E[n]` is finite**.
* `WeierstrassCurve.Affine.finite_torsion_of_charZero` : the characteristic-zero reading, with no
  hypothesis on `n` beyond `n ≠ 0`.
* `WeierstrassCurve.Affine.finite_torsion_of_lt_charP` : the positive-characteristic reading,
  `n < p`.
* `WeierstrassCurve.Affine.card_torsion_le_ladder` : the cardinality companion, `#E[n] ≤ 2·|S| + 1`
  for the same `S`.  ⚠️ Not `n²`; see above.
* `WeierstrassCurve.Affine.finite_torsion_five_y2EqX3AddOne` and
  `WeierstrassCurve.Affine.finite_torsion_five_algClosure` : the non-vacuity certificates, `E[5]`
  on `y² = x³ + 1` over `ℚ` and over `AlgebraicClosure ℚ` — an index no statement in this tree
  reached before.  ⚠️ The second is the one that carries weight; see its docstring.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and III.6,
  Corollary 6.4.
-/

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F]

variable (W : Affine F) in
/-- **The `x`-support the ladder predicts for `E[n]`**: the union of the root sets of `ΨSq_k` over
`2 ≤ k ≤ n`.

⚠️ The union starts at `k = 2`, not `k = 1`: `ΨSq₁ = 1` has no roots, so the `k = 1` rung of
`exists_ψ_evalEval_eq_zero_of_nsmul_eq_zero` is vacuous and including it would only add an empty
set.  ⚠️ And it is a union over *all* `k ≤ n`, not the single index `n`, because the ladder reports
that *some* rung vanishes without saying which — that is exactly the gap between this file and the
sharp `#E[n] ≤ n²`. -/
def ladderXSupport (n : ℕ) : Set F :=
  ⋃ k ∈ Set.Icc (2 : ℤ) (n : ℤ), {x : F | (W.ΨSq k).IsRoot x}

variable {W : Affine F}

/-- **The `x`-support is finite**, as a finite union of root sets of nonzero polynomials.

The hypothesis is what makes each `ΨSq_k` nonzero (`ΨSq_ne_zero`); ⚠️ without it a single `k` with
`(k : F) = 0` would contribute the zero polynomial, whose root set is all of `F`. -/
theorem finite_ladderXSupport {n : ℕ}
    (hchar : ∀ k : ℤ, 2 ≤ k → k ≤ (n : ℤ) → (k : F) ≠ 0) :
    (W.ladderXSupport n).Finite := by
  refine (Set.finite_Icc (2 : ℤ) (n : ℤ)).biUnion fun k hk => ?_
  exact finite_setOf_isRoot (W.ΨSq_ne_zero (hchar k hk.1 hk.2))

variable [DecidableEq F]

/-- **Every nonzero affine `n`-torsion point has its `x`-coordinate in `ladderXSupport n`.**

This is the supplier `EllipticCurves.Torsion.Finite`'s engine has been waiting for.  The ladder
gives a vanishing rung `ψ_k(x, y) = 0` with `1 ≤ k ≤ n`; `ψ_sq_evalEval` squares it into
`ΨSq_k(x) = 0`, a statement about `x` alone; and `k = 1` is impossible because `ψ₁ = 1`. -/
theorem mem_ladderXSupport_of_mem_torsion (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : 1 ≤ n)
    ⦃x y : F⦄ ⦃h : W.Nonsingular x y⦄ (hP : (.some x y h : W.Point) ∈ W.torsion n) :
    x ∈ W.ladderXSupport n := by
  obtain ⟨k, hk1, hkn, hψ⟩ :=
    exists_ψ_evalEval_eq_zero_of_nsmul_eq_zero h2 h hn (mem_torsion_iff.mp hP)
  have hroot : (W.ΨSq k).IsRoot x := by
    rw [IsRoot, ← ψ_sq_evalEval h.left k, hψ]
    ring
  have hk2 : 2 ≤ k := by
    by_contra hlt
    rw [show k = 1 by omega, ψ_one_evalEval] at hψ
    exact one_ne_zero hψ
  exact Set.mem_biUnion (Set.mem_Icc.mpr ⟨hk2, hkn⟩) hroot

/-- **`E[n]` is finite at every index `n ≥ 1`**, over a field in which `2, 3, …, n` are all
invertible.

⚠️ This is *finiteness only*.  The sharp `#E[n] ≤ n²` of `#252` needs the top rung `ΨSqₙ` on its
own and is not proved here; see the module docstring. -/
theorem finite_torsion_of_forall_intCast_ne_zero (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : 1 ≤ n)
    (hchar : ∀ k : ℤ, 2 ≤ k → k ≤ (n : ℤ) → (k : F) ≠ 0) :
    Finite (W.torsion n) :=
  W.finite_torsion_of_xCoords (finite_ladderXSupport hchar)
    (mem_ladderXSupport_of_mem_torsion h2 hn)

/-- **The cardinality companion**: `#E[n] ≤ 2·|ladderXSupport n| + 1`, from the two-points-per-fibre
count of `EllipticCurves.Torsion.Finite`.

⚠️ The right-hand side is **not** `n²`.  `ladderXSupport n` is a union of `n − 1` root sets of
degrees `3, 8, 15, …, n² − 1` (the degree of `ΨSq_k` is `k² − 1`), so it grows like `2n³/3`
rather than `n²` — ⚠️ a degree count, stated as
prose and **not** formalised anywhere below; the sharp count needs the top rung alone.  It is
recorded because a crude effective bound is still a bound, and because stating it makes the size of
the remaining gap visible rather than implicit. -/
theorem card_torsion_le_ladder (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : 1 ≤ n)
    (hchar : ∀ k : ℤ, 2 ≤ k → k ≤ (n : ℤ) → (k : F) ≠ 0) :
    Nat.card (W.torsion n) ≤ 2 * (W.ladderXSupport n).ncard + 1 :=
  W.card_torsion_le_of_xCoords (finite_ladderXSupport hchar)
    (mem_ladderXSupport_of_mem_torsion h2 hn)

/-- **`E[n]` is finite for every `n ≠ 0` over a field of characteristic zero.**

⚠️ This is the statement the `3`-smooth engine could not reach: `finite_torsion_of_smooth`
(`EllipticCurves.Torsion.Multiplicative`) is built from `#E[2] ≤ 4` and `#E[3] ≤ 9` by
multiplicativity and so says nothing at any `n` with a prime factor `≥ 5`. -/
theorem finite_torsion_of_charZero [CharZero F] {n : ℕ} (hn : 1 ≤ n) : Finite (W.torsion n) :=
  finite_torsion_of_forall_intCast_ne_zero (two_ne_zero) hn
    fun _ hk _ => Int.cast_ne_zero.mpr (by omega)

/-- **`E[n]` is finite whenever `n` is below the characteristic.**  The positive-characteristic
reading of `finite_torsion_of_forall_intCast_ne_zero`: `n < p` makes every `k ≤ n` prime to `p`. -/
theorem finite_torsion_of_lt_charP {p : ℕ} [CharP F p] {n : ℕ} (hn : 1 ≤ n) (hp : n < p) :
    Finite (W.torsion n) := by
  have key : ∀ k : ℤ, 2 ≤ k → k ≤ (n : ℤ) → (k : F) ≠ 0 := by
    intro k hk2 hkn hzero
    have hdvd : (p : ℤ) ∣ k := (CharP.intCast_eq_zero_iff F p k).mp hzero
    have hple : (p : ℤ) ≤ k := Int.le_of_dvd (by omega) hdvd
    omega
  rcases eq_or_lt_of_le hn with h1 | hlt
  · rw [← h1, torsion_one]
    infer_instance
  · exact finite_torsion_of_forall_intCast_ne_zero
      (by simpa using key 2 le_rfl (by exact_mod_cast hlt)) hn key

/-! ## Non-vacuity: an index the `3`-smooth engine cannot reach -/

section Nonvacuity

open EllipticCurves.Fixture

/-- **`E[5]` is finite for `y² = x³ + 1` over `ℚ`.**

⚠️ This is the point of the file in one line.  `5` has a prime factor `≥ 5`, so
`finite_torsion_of_smooth` (`EllipticCurves.Torsion.Multiplicative`) says nothing about `E[5]` on
any curve over any field — it is assembled from `#E[2] ≤ 4` and `#E[3] ≤ 9` by multiplicativity and
reaches no other prime.  Before this file the tree had no statement of this form at any index
outside `{2^a · 3^b}`.

⚠️ It is a finiteness statement and **not** a count: nothing here says `#E[5] ≤ 25`. -/
theorem finite_torsion_five_y2EqX3AddOne : Finite ((y2EqX3AddOne ℚ).torsion 5) :=
  finite_torsion_of_charZero (by norm_num)

open scoped Classical in
/-- **`E[5]` is finite over an algebraically closed field of characteristic zero**, where the group
is genuinely large.

⚠️ This is the certificate that carries weight, and `finite_torsion_five_y2EqX3AddOne` on its own
does not.  Over `ℚ` the group `E[5](ℚ)` is trivial, so finiteness there is true for reasons having
nothing to do with this file; over `AlgebraicClosure ℚ` it has `25` elements.  ⚠️ The count `25` is
**not** proved here — that is the `#E[n] ≤ n²` half plus a matching lower bound — only that the
group is finite. -/
theorem finite_torsion_five_algClosure :
    Finite ((y2EqX3AddOne (AlgebraicClosure ℚ)).torsion 5) :=
  finite_torsion_of_charZero (by norm_num)

end Nonvacuity

end WeierstrassCurve.Affine
