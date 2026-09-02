/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.NsmulOrder
import EllipticCurves.Torsion.TwoThreeDisjoint

/-!
# The order dictionary at a `2`-torsion point, and `[n]`-surjectivity at every `n`

`EllipticCurves.Torsion.NsmulOrder` proves `n • P = 0 ↔ ψₙ(P) = 0` at every point `P` that is
**not** `2`-torsion, and records the one case it leaves open:

> At a `2`-torsion point the forward implication is missing for odd `n`, and it reduces to a single
> fact: `Ψ₃(x) ≠ 0` at a root `x` of `Ψ₂Sq`.

`EllipticCurves.Torsion.TwoThreeDisjoint` supplies that fact.  **This file spends it**, and the
consequences run further than the missing case: with the dictionary at *every* point, the last
hypothesis of the `[n]`-surjectivity engine discharges itself.

## The `2`-torsion case is not the general induction

⚠️ `NsmulOrder`'s machinery is stated at a least vanishing index `d = e + 3 ≥ 3` and **none of it
is re-indexed here**, because at `d = 2` almost all of it is unnecessary.  The order of the point
is `2`, so the annihilator is the even numbers and there is nothing to discover about it; and `ψ`
vanishes at every even index unconditionally (`ψ_evalEval_eq_zero_of_ψ_two_evalEval_eq_zero`,
because `normEDS` carries an explicit factor `ψ₂` there).  What is left is one statement:

**at a `2`-torsion point `ψ` does not vanish at any odd index.**

That is a two-step induction on the odd numbers, driven by a single instance of
`ψ_mul_ψ_sub_of_ψ_eq_zero` at `d = 2`,

```
ψ_{n+2}·ψ_{n−2} = −ψ₃·ψ₁·ψₙ²   (ψ₁ = 1),
```

started at `ψ₁ = 1` and `ψ₃ ≠ 0`.  ⚠️ Compare the `d ≥ 3` route, where the same relator instance is
run through `ψ_evalEval_ne_zero_of_not_dvd` on a strong induction over the residues mod `d`: at
`d = 2` there is exactly one nonzero residue, so the strong induction collapses to a step of two.
`ψ_shift_step_of_ψ_eq_zero`, `divX_add_of_not_dvd` and the whole periodicity layer are **not used
here at all** — periodicity of `Φₙ/ΨSqₙ` is vacuous when every nonzero multiple of `P` is `P`.

## The price, and exactly where it is paid

⚠️ **`[W.IsElliptic]`, and nothing else.**  It enters at one point: `ψ₃(P) ≠ 0`, which is
`WeierstrassCurve.Affine.ψ_three_evalEval_ne_zero_of_ψ_two_evalEval_eq_zero`
(`EllipticCurves.Torsion.TwoThreeDisjoint`), resting on the Bézout certificate
`isCoprime_Ψ₃_Ψ₂Sq` whose combination lands on `C (Δ²)`.  Every statement below that does not need
it is stated without it — in particular `ψ_odd_evalEval_ne_zero_of_ψ_two_evalEval_eq_zero` takes
`ψ₃(P) ≠ 0` as a hypothesis and holds over any field, and
`two_nsmul_eq_zero_of_ψ_two_evalEval_eq_zero` needs neither the instance nor `(2 : F) ≠ 0`.

⚠️ *"This route needs `IsElliptic`"* is **not** *"the case is false without it"*.  Nothing here
measures that, and `NsmulOrder`'s instance-free
`nsmul_eq_zero_iff_ψ_evalEval_eq_zero` is deliberately left as it stands rather than weakened —
the unconditional statement below is a **new** theorem carrying the instance, not a re-signature of
the old one.

## The payoff: `hroot` discharges itself

`nsmul_surjective_of_root` (`NsmulOrder`) reduced `[n]`-surjectivity on `E(F̄)` to one input,

```
hroot :  ∀ x, ΨSqₙ(x) = 0 → Φₙ(x) ≠ 0,
```

recorded there as the pointwise weakening of `#1184` and explicitly not discharged.  **It is a
consequence of the dictionary at every point**, over an algebraically closed field:

* `ΨSqₙ(x) = 0` says `ψₙ(P) = 0` at a point `P` above `x` — which exists, and is nonsingular
  because the curve is elliptic;
* so `n • P = 0`, and then `ψ_{n±1}(P) ≠ 0`, because `(n ± 1) • P = 0` alongside `n • P = 0` forces
  `P = 0` and `P` is affine;
* and `Φₙ(x) ≠ 0` follows from the **merged** reduction
  `WeierstrassCurve.eval_Φ_ne_zero_of_eval_ΨSq_adjacent_ne_zero`
  (`EllipticCurves.DivisionPolynomial.Coprime`), which is exactly the statement that removes `Φ`
  from the problem.

⚠️ **This does not prove `#1184` over an arbitrary base**, which is the generality
`EllipticCurves.DivisionPolynomial.Coprime` works in: what is proved here is the *pointwise* shadow
of `IsCoprime (ΨSq_{n+1}·ΨSq_{n−1}) (ΨSq n)` over an algebraically closed field, obtained from the
group law rather than from a Bézout certificate.

⚠️ **It does, however, specialise back over a field** — an earlier version of this paragraph said
it did not, and that was wrong.  `Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed` makes
coprimality over a field *equivalent* to the absence of a common root in an algebraically closed
extension, so `eval_ΨSq_adjacent_ne_zero_of_eval_ΨSq_eq_zero` below descends to `IsCoprime` over
any field of characteristic `≠ 2`.  That is
`EllipticCurves.Torsion.CoprimeAdjacent.isCoprime_ΨSq_adjacent`, one file up.  What stays out of
reach is the arbitrary-**ring** form, which no route here touches.

⚠️ The `2`-torsion half of the dictionary is **load-bearing** for this, and that is why it was
worth closing: the point `P` produced above `x` is arbitrary, so a dictionary with a `ψ₂(P) ≠ 0`
side condition would leave `hroot` open at exactly the `x` where `Ψ₂Sq` vanishes.

## Main statements

* `WeierstrassCurve.Affine.ψ_odd_evalEval_ne_zero_of_ψ_two_evalEval_eq_zero` : at a `2`-torsion
  point, `ψ` does not vanish at an odd index — the whole of the new mathematics.
* `WeierstrassCurve.Affine.nsmul_eq_zero_iff_two_dvd_of_ψ_two_evalEval_eq_zero` : the dictionary at
  a `2`-torsion point, in its sharpest form — both `n • P = 0` and `ψₙ(P) = 0` are `2 ∣ n`.
* `WeierstrassCurve.Affine.nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic` : **`#251`'s scope
  item 2 at every point**, the `ψ₂(P) ≠ 0` hypothesis traded for `[W.IsElliptic]`.
* `WeierstrassCurve.Affine.eval_ΨSq_adjacent_ne_zero_of_eval_ΨSq_eq_zero` : at a root of `ΨSqₙ`
  neither neighbour `ΨSq_{n±1}` vanishes — the pointwise heart of the argument, and what
  `EllipticCurves.Torsion.CoprimeAdjacent` descends.
* `WeierstrassCurve.Affine.eval_Φ_ne_zero_of_eval_ΨSq_eq_zero` : `hroot`, discharged.
* `WeierstrassCurve.Affine.nsmul_surjective_of_two_ne_zero` : **`[n]` is surjective on `E(F̄)` at
  every `n ≠ 0`**, over an algebraically closed field of characteristic `≠ 2`, with no hypothesis
  left.
* `WeierstrassCurve.Affine.nsmul_eq_zero_iff_two_dvd_y2EqX3AddOne` : the certificate — a point at
  which `NsmulOrder`'s hypothesis provably fails and this file's dictionary still answers.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and Exercise 3.7.
-/

open Polynomial Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-! ## At a `2`-torsion point, `ψ` does not vanish at an odd index -/

/-- **`ψ` does not vanish at an odd index at a `2`-torsion point.**

The step is `ψ_mul_ψ_sub_of_ψ_eq_zero` at `d = 2`, which reads
`ψ_{n+2}·ψ_{n−2} = −ψ₃·ψ₁·ψₙ²` with `ψ₁ = 1`: if `ψ₃(x, y) ≠ 0` and `ψₙ(x, y) ≠ 0` then
`ψ_{n+2}(x, y) ≠ 0`.  Two rungs are needed to start it — `ψ₁ = 1` and the hypothesis `hψ₃` — so the
induction carries the pair `(2m + 1, 2m + 3)`.

⚠️ `hψ₃` is a hypothesis rather than an instance argument on purpose: this statement is true over
any field, and it is `ψ_three_evalEval_ne_zero_of_ψ_two_evalEval_eq_zero` that costs
`[W.IsElliptic]`. -/
theorem ψ_odd_evalEval_ne_zero_of_ψ_two_evalEval_eq_zero (ht : (W.ψ 2).evalEval x y = 0)
    (hψ₃ : (W.ψ 3).evalEval x y ≠ 0) (m : ℕ) :
    (W.ψ (2 * (m : ℤ) + 1)).evalEval x y ≠ 0 := by
  suffices h : ∀ k : ℕ, (W.ψ (2 * (k : ℤ) + 1)).evalEval x y ≠ 0 ∧
      (W.ψ (2 * (k : ℤ) + 3)).evalEval x y ≠ 0 from (h m).1
  intro k
  induction k with
  | zero =>
    refine ⟨?_, by simpa using hψ₃⟩
    simp only [Nat.cast_zero, mul_zero, zero_add, ψ_one_evalEval]
    exact one_ne_zero
  | succ k ih =>
    obtain ⟨-, hB⟩ := ih
    refine ⟨by push_cast; rwa [show 2 * ((k : ℤ) + 1) + 1 = 2 * (k : ℤ) + 3 by ring], ?_⟩
    have hstar := ψ_mul_ψ_sub_of_ψ_eq_zero (W := W) (x := x) (y := y) ht (2 * (k : ℤ) + 3)
    rw [show 2 * (k : ℤ) + 3 + 2 = 2 * (k : ℤ) + 5 by ring,
      show 2 * (k : ℤ) + 3 - 2 = 2 * (k : ℤ) + 1 by ring,
      show (2 : ℤ) + 1 = 3 by ring, show (2 : ℤ) - 1 = 1 by ring, ψ_one_evalEval] at hstar
    intro hcon
    push_cast at hcon
    rw [show 2 * ((k : ℤ) + 1) + 3 = 2 * (k : ℤ) + 5 by ring] at hcon
    rw [hcon, zero_mul] at hstar
    exact mul_ne_zero (mul_ne_zero hψ₃ one_ne_zero) (pow_ne_zero 2 hB) (by linear_combination hstar)

/-- **`ψₙ(x, y) = 0 ↔ n` is even, at a `2`-torsion point.**  The forward direction is
`ψ_odd_evalEval_ne_zero_of_ψ_two_evalEval_eq_zero`; the reverse is the unconditional
`ψ_evalEval_eq_zero_of_ψ_two_evalEval_eq_zero`, which holds because `normEDS` carries an explicit
factor `ψ₂` at every even index. -/
theorem ψ_evalEval_eq_zero_iff_two_dvd_of_ψ_two_evalEval_eq_zero (ht : (W.ψ 2).evalEval x y = 0)
    (hψ₃ : (W.ψ 3).evalEval x y ≠ 0) (n : ℕ) :
    (W.ψ (n : ℤ)).evalEval x y = 0 ↔ 2 ∣ n := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    refine ⟨fun _ => ⟨m, by ring⟩, fun _ => ?_⟩
    rw [show ((m + m : ℕ) : ℤ) = 2 * (m : ℤ) by push_cast; ring]
    exact ψ_evalEval_eq_zero_of_ψ_two_evalEval_eq_zero ht m
  · subst hm
    refine ⟨fun hz => absurd ?_ (ψ_odd_evalEval_ne_zero_of_ψ_two_evalEval_eq_zero ht hψ₃ m),
      fun hdvd => absurd hdvd (by omega)⟩
    rwa [show ((2 * m + 1 : ℕ) : ℤ) = 2 * (m : ℤ) + 1 by push_cast; ring] at hz

/-! ## The dictionary at a `2`-torsion point -/

section Point

variable [DecidableEq F]

/-- **`ψ₂(x, y) = 0` says `2 • (x, y) = 0`.**  `ψ₂ = 2y + a₁x + a₃ = y − negY x y`, so it vanishes
exactly when the point is its own negative.  ⚠️ No hypothesis on the characteristic: this is the
`d = 2` branch of `nsmul_eq_zero_of_minimal_ψ_evalEval_eq_zero` with the minimality and
`(2 : F) ≠ 0` hypotheses dropped, both of which that proof spends only on the `d ≥ 3` branch. -/
theorem two_nsmul_eq_zero_of_ψ_two_evalEval_eq_zero (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y = 0) : ((2 : ℕ) • Point.some x y hns : W.Point) = 0 := by
  rw [ψ_two_evalEval] at ht
  have hy : W.negY x y = y := by rw [negY]; linear_combination -ht
  have hneg : -(Point.some x y hns : W.Point) = Point.some x y hns := by
    rw [Point.neg_some, Point.some.injEq]
    exact ⟨rfl, hy⟩
  rw [two_nsmul]
  nth_rewrite 2 [← hneg]
  exact add_neg_cancel _

/-- **The full order dictionary at a `2`-torsion point**: the annihilator of the point and the
vanishing set of `ψ` are both the even numbers.

⚠️ This is the `2`-torsion analogue of `exists_order_of_exists_ψ_evalEval_eq_zero`, and it is
strictly sharper in shape: there the order is produced existentially in the `e + 3` form, here it
is the literal constant `2`. -/
theorem nsmul_eq_zero_iff_two_dvd_of_ψ_two_evalEval_eq_zero (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y = 0) (hψ₃ : (W.ψ 3).evalEval x y ≠ 0) (n : ℕ) :
    ((n • Point.some x y hns : W.Point) = 0 ↔ 2 ∣ n) ∧
      ((W.ψ (n : ℤ)).evalEval x y = 0 ↔ 2 ∣ n) := by
  refine ⟨⟨fun hz => ?_, fun ⟨m, hm⟩ => ?_⟩,
    ψ_evalEval_eq_zero_iff_two_dvd_of_ψ_two_evalEval_eq_zero ht hψ₃ n⟩
  · by_contra hc
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
    rw [mul_comm, add_nsmul, ← smul_smul, two_nsmul_eq_zero_of_ψ_two_evalEval_eq_zero hns ht,
      smul_zero, one_nsmul, zero_add] at hz
    exact Point.some_ne_zero hns hz
  · rw [hm, mul_comm, ← smul_smul, two_nsmul_eq_zero_of_ψ_two_evalEval_eq_zero hns ht, smul_zero]

/-- **`n • (x, y) = 0 ↔ ψₙ(x, y) = 0` at every point** — `#251`'s scope item 2, with no side
condition on the point.

⚠️ The trade against `nsmul_eq_zero_iff_ψ_evalEval_eq_zero` is exactly one hypothesis for one
instance: `ψ₂(x, y) ≠ 0` for `[W.IsElliptic]`.  That instance is spent only in the `2`-torsion
branch, and only on `ψ₃(x, y) ≠ 0`. -/
theorem nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    (hns : W.Nonsingular x y) (n : ℕ) :
    ((n • Point.some x y hns : W.Point) = 0) ↔ (W.ψ (n : ℤ)).evalEval x y = 0 := by
  by_cases ht : (W.ψ 2).evalEval x y = 0
  · have h := nsmul_eq_zero_iff_two_dvd_of_ψ_two_evalEval_eq_zero hns ht
      (ψ_three_evalEval_ne_zero_of_ψ_two_evalEval_eq_zero hns.left ht) n
    exact h.1.trans h.2.symm
  · exact nsmul_eq_zero_iff_ψ_evalEval_eq_zero h2 hns ht n

/-! ## The neighbours of a killing index do not vanish -/

/-- **`ψ_{n+1}(x, y) ≠ 0` when `n` kills the point.**  If it vanished, `(n + 1) • P` would be `0`
alongside `n • P`, and their difference is `P`. -/
theorem ψ_add_one_evalEval_ne_zero_of_nsmul_eq_zero [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    (hns : W.Nonsingular x y) {n : ℕ} (hz : (n • Point.some x y hns : W.Point) = 0) :
    (W.ψ ((n : ℤ) + 1)).evalEval x y ≠ 0 := by
  intro hcon
  have hsucc : ((n + 1 : ℕ) • Point.some x y hns : W.Point) = 0 := by
    refine (nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic h2 hns (n + 1)).mpr ?_
    rwa [show (((n + 1 : ℕ)) : ℤ) = (n : ℤ) + 1 by push_cast; ring]
  rw [succ_nsmul, hz, zero_add] at hsucc
  exact Point.some_ne_zero hns hsucc

/-- **`ψ_{n−1}(x, y) ≠ 0` when `n ≠ 0` kills the point.**  Same argument as
`ψ_add_one_evalEval_ne_zero_of_nsmul_eq_zero`, read at `n − 1`. -/
theorem ψ_sub_one_evalEval_ne_zero_of_nsmul_eq_zero [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    (hns : W.Nonsingular x y) {n : ℕ} (hn : n ≠ 0)
    (hz : (n • Point.some x y hns : W.Point) = 0) :
    (W.ψ ((n : ℤ) - 1)).evalEval x y ≠ 0 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
  intro hcon
  have hpred : ((k : ℕ) • Point.some x y hns : W.Point) = 0 := by
    refine (nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic h2 hns k).mpr ?_
    rwa [show ((k : ℕ) : ℤ) = (((k + 1 : ℕ)) : ℤ) - 1 by push_cast; ring]
  rw [succ_nsmul, hpred, zero_add] at hz
  exact Point.some_ne_zero hns hz

end Point

/-! ## The payoff: `hroot` is a theorem -/

/-- **At a root of `ΨSqₙ`, neither neighbour `ΨSq_{n±1}` vanishes**, over an algebraically closed
field of characteristic `≠ 2` on an elliptic curve.

The route is the dictionary, not a Bézout certificate: a root `x` of `ΨSqₙ` carries a point
`(x, y)` of `W`, which is then killed by `n`, and `ψ_{n±1}(x, y) ≠ 0` because `(n ± 1) • P = 0`
alongside `n • P = 0` would force `P = 0` while `P` is affine.

⚠️ This is the *pointwise* form of `IsCoprime (ΨSq_{n+1} · ΨSq_{n−1}) (ΨSq n)`, not that statement
— which is `#1184` and is proved over an arbitrary commutative ring nowhere in this development.
⚠️ Over a **field** it does descend to the `IsCoprime` form, in
`EllipticCurves.Torsion.CoprimeAdjacent`; the module docstring above says which half of `#1184`
that closes and which it does not. -/
theorem eval_ΨSq_adjacent_ne_zero_of_eval_ΨSq_eq_zero [IsAlgClosed F] [W.IsElliptic]
    (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0) {x : F} (hΨ : (W.ΨSq (n : ℤ)).eval x = 0) :
    (W.ΨSq ((n : ℤ) + 1)).eval x * (W.ΨSq ((n : ℤ) - 1)).eval x ≠ 0 := by
  classical
  obtain ⟨y, hxy⟩ := exists_equation (W := W) h2 x
  have hns : W.Nonsingular x y := equation_iff_nonsingular.mp hxy
  have hψn : (W.ψ (n : ℤ)).evalEval x y = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by rw [ψ_sq_evalEval hxy, hΨ])
  have hz : ((n : ℕ) • Point.some x y hns : W.Point) = 0 :=
    (nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic h2 hns n).mpr hψn
  refine mul_ne_zero ?_ ?_
  · rw [← ψ_sq_evalEval hxy]
    exact pow_ne_zero 2 (ψ_add_one_evalEval_ne_zero_of_nsmul_eq_zero h2 hns hz)
  · rw [← ψ_sq_evalEval hxy]
    exact pow_ne_zero 2 (ψ_sub_one_evalEval_ne_zero_of_nsmul_eq_zero h2 hns hn hz)

/-- **`Φₙ` and `ΨSqₙ` have no common root over an algebraically closed field of characteristic
`≠ 2`.**  This is the remaining input `hroot` of
`WeierstrassCurve.Affine.nsmul_surjective_of_root`, recorded there as the pointwise weakening of
`#1184`.

⚠️ The whole of the work is `eval_ΨSq_adjacent_ne_zero_of_eval_ΨSq_eq_zero` above; the step from
the two neighbours to `Φₙ` is the merged, hypothesis-free
`WeierstrassCurve.eval_Φ_ne_zero_of_eval_ΨSq_adjacent_ne_zero`
(`EllipticCurves.DivisionPolynomial.Coprime`), which is exactly the statement that removes `Φ` from
the problem. -/
theorem eval_Φ_ne_zero_of_eval_ΨSq_eq_zero [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    {n : ℕ} (hn : n ≠ 0) (x : F) (hΨ : (W.ΨSq (n : ℤ)).eval x = 0) :
    (W.Φ (n : ℤ)).eval x ≠ 0 :=
  WeierstrassCurve.eval_Φ_ne_zero_of_eval_ΨSq_adjacent_ne_zero hΨ
    (eval_ΨSq_adjacent_ne_zero_of_eval_ΨSq_eq_zero h2 hn hΨ)

section Surjective

variable [DecidableEq F]

/-- **Multiplication by `n` is surjective on `E(F̄)`, at every `n ≠ 0`**, over an algebraically
closed field of characteristic `≠ 2` — with no remaining hypothesis.

⚠️ This is where the `2`-torsion half of the dictionary pays for itself.
`eval_Φ_ne_zero_of_eval_ΨSq_eq_zero` lifts an arbitrary root of `ΨSqₙ` to a point, and nothing
controls whether that point is
`2`-torsion; a dictionary carrying `ψ₂(P) ≠ 0` would leave the argument open at exactly the roots
of `Ψ₂Sq`. -/
theorem nsmul_surjective_of_two_ne_zero [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) : Function.Surjective fun P : W.Point => n • P :=
  nsmul_surjective_of_root h2 hn (eval_Φ_ne_zero_of_eval_ΨSq_eq_zero h2 hn)

end Surjective

/-! ## Non-vacuity: the dictionary run at a point where the old one is silent -/

section Nonvacuity

open EllipticCurves.Fixture

/-- `(−1, 0)` lies on `y² = x³ + 1` over `ℚ` and is nonsingular. -/
private lemma exampleNonsingularNegOneZero : (y2EqX3AddOne ℚ).Nonsingular (-1) 0 :=
  equation_iff_nonsingular.mp
    (by norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff])

/-- **The certificate.**  At `(−1, 0)` on `y² = x³ + 1` over `ℚ` the hypothesis
`ψ₂(P) ≠ 0` of `WeierstrassCurve.Affine.nsmul_eq_zero_iff_ψ_evalEval_eq_zero` **fails** — that is
the first conjunct, machine-checked here rather than asserted — and the dictionary of this file
still computes the whole annihilator: `n • (−1, 0) = 0` exactly when `n` is even.

⚠️ The `[W.IsElliptic]` instance is found rather than assumed, and it is the only thing traded for
the missing hypothesis. -/
theorem nsmul_eq_zero_iff_two_dvd_y2EqX3AddOne :
    ((y2EqX3AddOne ℚ).ψ 2).evalEval (-1) 0 = 0 ∧
      ∀ n : ℕ, ((n • Point.some (-1) 0 exampleNonsingularNegOneZero :
        (y2EqX3AddOne ℚ).Point) = 0 ↔ 2 ∣ n) :=
  ⟨ψ_three_ne_zero_two_torsion_y2EqX3AddOne.1, fun n =>
    (nsmul_eq_zero_iff_two_dvd_of_ψ_two_evalEval_eq_zero exampleNonsingularNegOneZero
      ψ_three_ne_zero_two_torsion_y2EqX3AddOne.1
      (ψ_three_evalEval_ne_zero_of_ψ_two_evalEval_eq_zero exampleNonsingularNegOneZero.left
        ψ_three_ne_zero_two_torsion_y2EqX3AddOne.1) n).1⟩

/-- The unconditional dictionary, at the same point.  ⚠️ `ψ₃(−1, 0) = −9 ≠ 0`, so the odd indices
really are where the content is: `3 • (−1, 0) ≠ 0`. -/
example : ((3 : ℕ) • Point.some (-1) 0 exampleNonsingularNegOneZero :
    (y2EqX3AddOne ℚ).Point) ≠ 0 := fun h =>
  absurd (nsmul_eq_zero_iff_two_dvd_y2EqX3AddOne.2 3 |>.mp h) (by omega)

end Nonvacuity

end WeierstrassCurve.Affine
