/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.Finite
import EllipticCurves.Torsion.NsmulOrder

/-!
# The `x`-support of `E[n]`, and the sharp bound `#E[n] ≤ n²`

`EllipticCurves.Torsion.Finite` is a *counting engine*: it turns "the nonzero `n`-torsion points
have their `x`-coordinates in a finite set `S`" into `Finite E[n]` and `#E[n] ≤ 2·|S| + 1`.  This
file supplies the support and spends the engine.

The supplier is `WeierstrassCurve.Affine.ψ_evalEval_eq_zero_of_nsmul_eq_zero`
(`EllipticCurves.Torsion.NsmulOrder`): if `n • P = 0` for an affine `P = (x, y)` then `ψₙ(x, y) = 0`
at the index `n` itself.  Squaring with `ψ_sq_evalEval` moves it onto the `x`-axis, `ΨSqₙ(x) = 0`,
so every nonzero `n`-torsion point has its `x`-coordinate in the root set of the *single* nonzero
univariate polynomial `ΨSqₙ`, of degree `n² − 1`.

## Getting from `2n² − 1` to `n²`

The root set of `ΨSqₙ` and the two-points-per-fibre count give `#E[n] ≤ 2(n² − 1) + 1 = 2n² − 1`,
which is off by a factor of two.  Both halves of that factor are recovered by looking at how
`ΨSqₙ` factors, and neither is a new theorem about torsion:

* **`ΨSqₙ` is a square, up to `Ψ₂Sq`.**  It is so *by Mathlib's definition*:
  `ΨSqₙ = preΨₙ² · Ψ₂Sq` at even `n` and `ΨSqₙ = preΨₙ²` at odd `n`.  So its distinct roots are
  those of `preΨₙ`, whose degree is bounded by `(n² − 1)/2` at odd `n` and `(n² − 4)/2` at even
  `n` (`natDegree_preΨ_le`), together with, at even `n`, the at most three roots of `Ψ₂Sq`
  (`natDegree_Ψ₂Sq_le`).  Half the degree, so half the count.
* **Over a root of `Ψ₂Sq` the fibre is a singleton.**  `Ψ₂Sq(x) = ψ₂(x, y)²` and
  `ψ₂ = 2y + a₁x + a₃ = y − negY x y`, so a point above such an `x` is its own negative, and the
  two-per-fibre count of `ncard_le_of_xCoords` overcounts it.  `ncard_le_of_xCoords_of_selfNeg`
  (added to `EllipticCurves.Torsion.Finite` for this file) counts those fibres once.

At odd `n` the first point alone gives `2·(n² − 1)/2 + 1 = n²`.  At even `n` both are needed:
`2·(n² − 4)/2 + 3 + 1 = n²`.  ⚠️ The arithmetic lands on `n²` exactly, with nothing to spare — at
`n = 2` it reads `2·0 + 3 + 1 = 4` (`preΨ₂ = 1` has no roots), and `card_torsion_two_of_splits`
(`EllipticCurves.Torsion.TwoTorsion`) shows `4` is attained whenever `Ψ₂Sq` splits.

## ⚠️ What is and is not proved here

`#E[n] ≤ n²` is an **upper** bound.  The matching `≥` is not here and does not follow from
anything below: it is the `#E[n] = n²` gate that `EllipticCurves.Torsion.PrimaryTower` takes as a
hypothesis, and `#1490` records that it does not follow from surjectivity of `[n]` either.  ⚠️ That
gate is discharged elsewhere at odd `n` — `card_torsion_eq_sq_of_odd`
(`EllipticCurves.Torsion.OmegaChordSum`), through the separability route of
`EllipticCurves.Torsion.OddTorsionCount`, which consumes the bound proved here.  Nothing in this
file changes, and the `≥` half is still not among its conclusions.

## ⚠️ The characteristic hypotheses, and where each is spent

Two, and they are the textbook ones:

* `(2 : F) ≠ 0` is the hypothesis `ψ_evalEval_eq_zero_of_nsmul_eq_zero` itself carries.  ⚠️ It is
  spent a second time here, on `Ψ₂Sq ≠ 0`: Mathlib's `Ψ₂Sq_ne_zero` asks for `(4 : F) ≠ 0`, which
  is `Ψ₂Sq`'s leading coefficient (`leadingCoeff_Ψ₂Sq`).
* `(n : F) ≠ 0`, i.e. `char F ∤ n`, is what makes `ΨSqₙ` and `preΨₙ` nonzero polynomials — a
  *zero* polynomial has every element of `F` as a root and the support would be all of `F`.

⚠️ This file supersedes `EllipticCurves.Torsion.FiniteLadder`, which is deleted by the same change.
That file ran on `exists_ψ_evalEval_eq_zero_of_nsmul_eq_zero` — *some* rung `k ≤ n` of the ladder
vanishes, without saying which — and so had to take the union of the root sets of `ΨSq₂, …, ΨSqₙ`.
It paid twice for that: the support grew like `n³/3` rather than `n² − 1`, giving finiteness but no
`n²` bound; and it needed `(k : F) ≠ 0` for **every** `2 ≤ k ≤ n`, i.e. `char F = 0` or
`char F > n`, rather than `char F ∤ n`.  Both prices had the same cause, and the top-rung supplier
refunds both.  Nothing outside that file consumed any of its declarations — only the root import
named it.  What is deleted is `ladderXSupport`, `finite_ladderXSupport`,
`mem_ladderXSupport_of_mem_torsion`, `card_torsion_le_ladder` and
`finite_torsion_of_forall_intCast_ne_zero`, the last superseded by
`finite_torsion_of_intCast_ne_zero` below under strictly weaker hypotheses.
`finite_torsion_of_charZero`, `finite_torsion_of_lt_charP` and the two `E[5]` certificates reappear
below with their names and statements unchanged.

## Main definitions

* `WeierstrassCurve.Affine.torsionXSupport` : the `x`-support, `{x | ΨSqₙ(x) = 0}`.

## Main statements

* `WeierstrassCurve.Affine.finite_torsionXSupport`,
  `WeierstrassCurve.Affine.ncard_torsionXSupport_le` : it is finite, with at most `n² − 1` elements.
* `WeierstrassCurve.Affine.mem_torsionXSupport_of_mem_torsion` : it contains the `x`-coordinate of
  every nonzero affine `n`-torsion point.  Together with the previous two this is the package
  `#251`'s scope item 3 asks for.
* `WeierstrassCurve.Affine.card_torsion_le_sq` : **`#E[n] ≤ n²`**, the headline of `#246`.
* `WeierstrassCurve.Affine.finite_torsion_of_intCast_ne_zero`,
  `WeierstrassCurve.Affine.finite_torsion_of_charZero`,
  `WeierstrassCurve.Affine.finite_torsion_of_not_dvd_charP`,
  `WeierstrassCurve.Affine.finite_torsion_of_lt_charP` : `E[n]` is finite, in four readings.
* `WeierstrassCurve.Affine.card_torsion_five_le_algClosure` : the non-vacuity certificate,
  `#E[5] ≤ 25` on `y² = x³ + 1` over `AlgebraicClosure ℚ`, where the true count is `25`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and III.6,
  Corollary 6.4.
-/

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-- A nonzero polynomial over a field has at most `natDegree` many distinct roots.  ⚠️ Mathlib has
this for the root *multiset* (`Polynomial.card_roots'`) and finiteness of the root *set*
(`Polynomial.finite_setOf_isRoot`), but not the `Set.ncard` bound the counting engine consumes. -/
private theorem ncard_setOf_isRoot_le {p : F[X]} (hp : p ≠ 0) :
    {x : F | p.IsRoot x}.ncard ≤ p.natDegree := by
  classical
  have hset : {x : F | p.IsRoot x} = (p.roots.toFinset : Set F) := by
    ext x; simp [mem_roots hp]
  rw [hset, Set.ncard_coe_finset]
  exact (Multiset.toFinset_card_le _).trans p.card_roots'

private theorem four_ne_zero (h2 : (2 : F) ≠ 0) : (4 : F) ≠ 0 := by
  have : (4 : F) = 2 * 2 := by norm_num
  rw [this]
  exact mul_ne_zero h2 h2

variable (W) in
/-- **The `x`-support of `E[n]`**: the root set of the single univariate polynomial `ΨSqₙ`.

⚠️ It is indexed by `n : ℤ` because `ΨSq` is, and `ΨSq (-n) = ΨSq n`; the torsion statements below
instantiate it at a natural number. -/
def torsionXSupport (n : ℤ) : Set F := {x : F | (W.ΨSq n).IsRoot x}

/-- **The `x`-support is finite.**  The hypothesis is what makes `ΨSqₙ` a nonzero polynomial;
⚠️ without it the support is all of `F`. -/
theorem finite_torsionXSupport {n : ℤ} (hn : (n : F) ≠ 0) : (W.torsionXSupport n).Finite :=
  finite_setOf_isRoot (W.ΨSq_ne_zero hn)

/-- **The `x`-support has at most `n² − 1` elements**, the degree of `ΨSqₙ`. -/
theorem ncard_torsionXSupport_le {n : ℤ} (hn : (n : F) ≠ 0) :
    (W.torsionXSupport n).ncard ≤ n.natAbs ^ 2 - 1 :=
  (ncard_setOf_isRoot_le (W.ΨSq_ne_zero hn)).trans (W.natDegree_ΨSq_le n)

/-- **At an odd index the `x`-support is the root set of `preΨₙ`.**  `ΨSqₙ = preΨₙ²` there, and a
field has no zero divisors, so the two polynomials have the same roots — but `preΨₙ` carries half
the degree bound.  ⚠️ This is where the factor of two in `#E[n] ≤ n²` comes from at odd `n`. -/
theorem torsionXSupport_of_odd {n : ℤ} (hodd : Odd n) :
    W.torsionXSupport n = {x : F | (W.preΨ n).IsRoot x} := by
  ext x
  simp [torsionXSupport, ΨSq, Int.not_even_iff_odd.mpr hodd, IsRoot, pow_eq_zero_iff]

/-- **A point above a root of `Ψ₂Sq` is its own negative.**  `Ψ₂Sq(x) = ψ₂(x, y)²` and
`ψ₂ = 2y + a₁x + a₃ = y − negY x y`.  ⚠️ This is what lets the counting engine charge one point,
not two, to each such `x`, and it is the second half of the factor of two at an even index. -/
theorem selfNeg_of_isRoot_Ψ₂Sq {x y : F} (h : W.Equation x y) (hx : W.Ψ₂Sq.IsRoot x) :
    y = W.negY x y := by
  have hsq := ψ_sq_evalEval h 2
  rw [WeierstrassCurve.ΨSq_two, hx] at hsq
  have h0 : (W.ψ 2).evalEval x y = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  rw [ψ_two_evalEval] at h0
  rw [negY]
  linear_combination h0

variable [DecidableEq F]

/-- **Every nonzero affine `n`-torsion point has its `x`-coordinate in `torsionXSupport n`.**

This is the supplier `EllipticCurves.Torsion.Finite`'s engine has been waiting for since it merged:
`ψ_evalEval_eq_zero_of_nsmul_eq_zero` gives `ψₙ(x, y) = 0` at the index `n` itself, and
`ψ_sq_evalEval` squares it into `ΨSqₙ(x) = 0`. -/
theorem mem_torsionXSupport_of_mem_torsion (h2 : (2 : F) ≠ 0) {n : ℕ}
    ⦃x y : F⦄ ⦃h : W.Nonsingular x y⦄ (hP : (.some x y h : W.Point) ∈ W.torsion n) :
    x ∈ W.torsionXSupport (n : ℤ) := by
  have hψ := ψ_evalEval_eq_zero_of_nsmul_eq_zero h2 h (mem_torsion_iff.mp hP)
  have hsq := ψ_sq_evalEval h.left (n : ℤ)
  rw [hψ] at hsq
  simpa [torsionXSupport, IsRoot] using hsq.symm

/-- The even-index form of `mem_torsionXSupport_of_mem_torsion`: the `x`-coordinate is a root of
`preΨₙ` **or** of `Ψ₂Sq`, from the factorisation `ΨSqₙ = preΨₙ² · Ψ₂Sq`.  ⚠️ Stated at every `n`
rather than only at even `n`, because that is the shape `card_torsion_le_of_xCoords_of_selfNeg`
consumes; at odd `n` the proof always takes the first alternative, since the second factor of
`ΨSqₙ` is then the constant `1`. -/
theorem mem_preΨ_union_Ψ₂Sq_of_mem_torsion (h2 : (2 : F) ≠ 0) {n : ℕ}
    ⦃x y : F⦄ ⦃h : W.Nonsingular x y⦄ (hP : (.some x y h : W.Point) ∈ W.torsion n) :
    x ∈ {x : F | (W.preΨ (n : ℤ)).IsRoot x} ∪ {x : F | W.Ψ₂Sq.IsRoot x} := by
  have hx := mem_torsionXSupport_of_mem_torsion h2 hP
  rw [torsionXSupport, Set.mem_setOf_eq, IsRoot, ΨSq, eval_mul, eval_pow] at hx
  rcases mul_eq_zero.mp hx with hp | hq
  · exact Or.inl (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hp)
  · by_cases he : Even (n : ℤ)
    · rw [if_pos he] at hq
      exact Or.inr hq
    · rw [if_neg he] at hq
      simp at hq

/-- **`E[n]` is finite** over a field with `(2 : F) ≠ 0` whenever `char F ∤ n`. -/
theorem finite_torsion_of_intCast_ne_zero (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : (n : F) ≠ 0) :
    Finite (W.torsion n) :=
  W.finite_torsion_of_xCoords (finite_torsionXSupport (by exact_mod_cast hn))
    (mem_torsionXSupport_of_mem_torsion h2)

/-- **`#E[n] ≤ n²`** over a field with `(2 : F) ≠ 0` whenever `char F ∤ n` — the headline of `#246`.

The two parities take different routes to the same number: at odd `n` the support is the root set
of `preΨₙ`, of degree `(n² − 1)/2`, and two points per fibre plus `O` give `n²`; at even `n` the
support splits as the roots of `preΨₙ`, of degree `(n² − 4)/2`, together with the at most three
roots of `Ψ₂Sq`, which carry one point each rather than two, giving `(n² − 4) + 3 + 1 = n²`.

⚠️ This is the **upper** bound only.  The matching `≥` is a separate gate; see the module
docstring. -/
theorem card_torsion_le_sq (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : (n : F) ≠ 0) :
    Nat.card (W.torsion n) ≤ n ^ 2 := by
  have hn' : ((n : ℤ) : F) ≠ 0 := by exact_mod_cast hn
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hdeg := (ncard_setOf_isRoot_le (W.preΨ_ne_zero hn')).trans (W.natDegree_preΨ_le (n : ℤ))
  rw [Int.natAbs_natCast] at hdeg
  rcases Nat.even_or_odd n with he | ho
  -- Even `n`: the roots of `Ψ₂Sq` are the `x`-coordinates of `2`-torsion points and are charged
  -- one point each.
  · rw [if_pos (by exact_mod_cast he : Even ((n : ℤ)))] at hdeg
    have h₀ := (ncard_setOf_isRoot_le (W.Ψ₂Sq_ne_zero (four_ne_zero h2))).trans W.natDegree_Ψ₂Sq_le
    have hcard := W.card_torsion_le_of_xCoords_of_selfNeg (n := n)
      (finite_setOf_isRoot (W.preΨ_ne_zero hn'))
      (finite_setOf_isRoot (W.Ψ₂Sq_ne_zero (four_ne_zero h2)))
      (mem_preΨ_union_Ψ₂Sq_of_mem_torsion h2)
      (fun _ _ hns _ hx => selfNeg_of_isRoot_Ψ₂Sq hns.left hx)
    obtain ⟨m, rfl⟩ := he
    have hsq : (m + m) ^ 2 = 4 * m ^ 2 := by ring
    have hm : 1 ≤ m := by omega
    rw [hsq] at hdeg ⊢
    have : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  -- Odd `n`: the support is the root set of `preΨₙ` outright.
  · have hoZ : Odd ((n : ℤ)) := by exact_mod_cast ho
    rw [if_neg (Int.not_even_iff_odd.mpr hoZ)] at hdeg
    have hcard := W.card_torsion_le_of_xCoords (finite_setOf_isRoot (W.preΨ_ne_zero hn'))
      (fun _ _ _ hP => by
        have := mem_torsionXSupport_of_mem_torsion h2 hP
        rwa [torsionXSupport_of_odd hoZ] at this)
    obtain ⟨m, rfl⟩ := ho
    have hsq : (2 * m + 1) ^ 2 = 4 * m ^ 2 + 4 * m + 1 := by ring
    rw [hsq] at hdeg ⊢
    omega

/-- **`E[n]` is finite for every `n ≠ 0` over a field of characteristic zero.** -/
theorem finite_torsion_of_charZero [CharZero F] {n : ℕ} (hn : 1 ≤ n) : Finite (W.torsion n) :=
  finite_torsion_of_intCast_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (by omega))

/-- **`#E[n] ≤ n²` over a field of characteristic zero**, with no hypothesis beyond `n ≠ 0`. -/
theorem card_torsion_le_sq_of_charZero [CharZero F] {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (W.torsion n) ≤ n ^ 2 :=
  card_torsion_le_sq two_ne_zero (Nat.cast_ne_zero.mpr (by omega))

/-- **`E[n]` is finite whenever the characteristic does not divide `n`.**  ⚠️ `(2 : F) ≠ 0` is a
separate hypothesis and is not implied by `¬ p ∣ n`: it is `p ≠ 2`, which is about the field and
not about `n`. -/
theorem finite_torsion_of_not_dvd_charP (h2 : (2 : F) ≠ 0) {p : ℕ} [CharP F p] {n : ℕ}
    (hn : ¬ p ∣ n) : Finite (W.torsion n) :=
  finite_torsion_of_intCast_ne_zero h2 fun h => hn ((CharP.cast_eq_zero_iff F p n).mp h)

/-- **`E[n]` is finite whenever `n` is below the characteristic**, the reading that needs no
separate `(2 : F) ≠ 0`: `n < p` supplies both `¬ p ∣ n` and `¬ p ∣ 2`. -/
theorem finite_torsion_of_lt_charP {p : ℕ} [CharP F p] {n : ℕ} (hn : 1 ≤ n) (hp : n < p) :
    Finite (W.torsion n) := by
  have hdvd : ∀ m : ℕ, 1 ≤ m → m < p → ¬ p ∣ m := fun m hm hmp hd =>
    absurd (Nat.le_of_dvd (by omega) hd) (by omega)
  rcases eq_or_lt_of_le hn with h1 | hlt
  · rw [← h1, torsion_one]
    infer_instance
  · exact finite_torsion_of_not_dvd_charP
      (fun h => hdvd 2 (by omega) (by omega) ((CharP.cast_eq_zero_iff F p 2).mp h))
      (hdvd n hn hp)

/-! ## Non-vacuity: an index the `3`-smooth engine cannot reach, now with a count -/

section Nonvacuity

open EllipticCurves.Fixture

/-- **`E[5]` is finite for `y² = x³ + 1` over `ℚ`.**

⚠️ `5` has a prime factor `≥ 5`, so `finite_torsion_of_smooth`
(`EllipticCurves.Torsion.Multiplicative`) says nothing about `E[5]` on any curve over any field —
it is assembled from `#E[2] ≤ 4` and `#E[3] ≤ 9` by multiplicativity and reaches no other prime.

⚠️ On its own this certificate carries no weight: over `ℚ` the group `E[5](ℚ)` is trivial, so
finiteness there is true for reasons having nothing to do with this file.  See
`card_torsion_five_le_algClosure`. -/
theorem finite_torsion_five_y2EqX3AddOne : Finite ((y2EqX3AddOne ℚ).torsion 5) :=
  finite_torsion_of_charZero (by norm_num)

open scoped Classical in
/-- **`E[5]` is finite over an algebraically closed field of characteristic zero**, where the group
is genuinely large. -/
theorem finite_torsion_five_algClosure :
    Finite ((y2EqX3AddOne (AlgebraicClosure ℚ)).torsion 5) :=
  finite_torsion_of_charZero (by norm_num)

open scoped Classical in
/-- **`#E[5] ≤ 25` on `y² = x³ + 1` over `AlgebraicClosure ℚ`.**

⚠️ This is the certificate that carries weight, and `finite_torsion_five_y2EqX3AddOne` on its own
does not: over `ℚ` the group `E[5](ℚ)` is trivial, while over `AlgebraicClosure ℚ` the classical
count is `25` ([J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6,
Corollary 6.4), so the bound is attained there.
⚠️ That count is a *reference*, not a theorem of this tree: the matching `≥ 25` is proved neither
here nor anywhere below.  See the module docstring. -/
theorem card_torsion_five_le_algClosure :
    Nat.card ((y2EqX3AddOne (AlgebraicClosure ℚ)).torsion 5) ≤ 25 := by
  simpa using card_torsion_le_sq_of_charZero
    (W := y2EqX3AddOne (AlgebraicClosure ℚ)) (n := 5) (by norm_num)

end Nonvacuity

end WeierstrassCurve.Affine
