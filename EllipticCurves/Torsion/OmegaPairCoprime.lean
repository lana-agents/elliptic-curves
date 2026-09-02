/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.Torsion.NsmulYPeriodic
import EllipticCurves.Torsion.WronskianSeparable

/-!
# `IsCoprime (preΨₙ) (preΩₙ)` at odd `n` — `#1506` scope item 2, discharged

`EllipticCurves.Torsion.WronskianSeparable` reduced `#E[n] = n²` at odd `n` to **two** equations:
the Wronskian form of `[n]∗ω = nω`, and the pointwise identity it calls `hpair`,

```
ψ_{n+2}·ψ_{n−1}²  =  −ψ_{n−2}·ψ_{n+1}²      at a point of `W` where `ψₙ` vanishes.
```

**This file proves `hpair`**, and therefore `IsCoprime (preΨₙ) (preΩₙ)` outright.  What is left of
`#1506` — and so of `#1490` item 3, `#E[p] = p²` at `p ≥ 5` — is the Wronskian identity **alone**.

## The route, in one paragraph

Write `Wₘ := ψ_{m+n}/ψₘ` at a point where `ψₙ` vanishes.  Ward's relation in the form
`WeierstrassCurve.Affine.ψ_shift_symm_of_ψ_eq_zero` (`EllipticCurves.Torsion.NsmulYPeriodic`) says
`W_{m+k}·W_{m−k} = Wₘ²`, so `W` is "geometric", `Wₘ = A·Bᵐ`; and `hpair` is exactly
`W₂·W₋₁² = W₋₂·W₁²`, both sides being `A³`.  ⚠️ **That derivation is not a proof** — it crosses the
index `0`, where `W₀ = ψₙ/ψ₀` is undefined.  And the obvious ways to avoid `0` prove only half of
it: every combination one writes down first carries an **even** coefficient on the target, and so
gives the squared form `(ψ_{n+2}ψ_{n−1}²)² = (ψ_{n−2}ψ_{n+1}²)²`, which does not pin the sign.

⚠️ `#1506` proposed a squared congruence, `preΩₙ² ≡ −4·Ψ₂Sq²·(preΨ_{n+1}preΨ_{n−1})³ (mod preΨₙ)`,
as *its* route.  That is a different argument for the same coprimality — it recovers `preΩₙ` as a
unit mod `preΨₙ` from its square — and it is not what is done here: it does not give `hpair`, and
`hpair` is what `EllipticCurves.Torsion.WronskianSeparable` consumes.

What does pin the sign is a single integer identity between three instances of the relation:

```
u₂ + 2u₋₁ − u₋₂ − 2u₁  =  −R(1,3) + R(3,1) + 2·R(1,2)     with  R(m,k) : u_{m+k} + u_{m−k} = 2uₘ,
```

which is a `ℤ`-combination — not a `ℚ`-one — and so survives multiplicatively.  Cleared of
denominators it is `WeierstrassCurve.Affine.ψ_pair_mul_of_ψ_eq_zero` below:

```
ψ_{n+4} · ψ₃² · (ψ_{n+2}·ψ_{n−1}² + ψ_{n−2}·ψ_{n+1}²)  =  0,
```

with **no** hypothesis beyond `ψₙ(x, y) = 0` — no characteristic, no nonsingularity, no `n` odd.
`hpair` is then that identity divided by `ψ_{n+4}·ψ₃²`.

## Where the two divisors come from, and the one point at which they fail

At a point of order `d` the order dictionary of `EllipticCurves.Torsion.NsmulOrder` says `ψₘ`
vanishes exactly at the multiples of `d`.  With `n` odd and `ψₙ = 0` we get `d ∣ n`, so `d` is odd;
then `d ∤ n + 4` (else `d ∣ 4`, and `d ≥ 3` is odd), which gives `ψ_{n+4} ≠ 0`, and `ψ₃ ≠ 0` as soon
as `d ≠ 3`.

⚠️ **`d = 3` is a genuine exception and needs the curve, not Ward.**  There `Wₘ` is undefined at
every multiple of `3`, and no combination of the relations reaches `hpair`: this is the same
obstruction that `EllipticCurves.Torsion.NsmulYPeriodic` records for the `y`-periodicity, where
`divT_add_three_of_ψ_three_eq_zero` also had to be proved separately.  The input here is the same
one — `ψ_add_three_evalEval_of_ψ_three_eq_zero`, `ψ_{m+3} = −ψ₂^{2m+3}·ψₘ` — from which

```
ψ_{3j+2}³ = ψ₂^{6j+3} · ψ_{3j+1}³
```

follows by induction on `j`, and `hpair` at `n = 3j + 3` is that identity times `−ψ₂^{6j+7}`.

## Main statements

⚠️ Every public declaration of this file is listed.

* `WeierstrassCurve.Affine.ψ_pair_mul_of_ψ_eq_zero` : the cleared identity, at every `n : ℤ` and
  with no hypothesis but `ψₙ(x, y) = 0`.
* `WeierstrassCurve.Affine.ψ_pair_of_ψ_eq_zero` : `hpair` at a nonsingular point which is not
  `2`-torsion, at odd `n`.
* `WeierstrassCurve.Affine.ψ_pair_of_equation` : `hpair` in exactly the shape
  `EllipticCurves.Torsion.WronskianSeparable` asks for — quantified over the points of `W`, with
  the `ψ₂ ≠ 0` and nonsingularity side conditions discharged.
* `WeierstrassCurve.Affine.isCoprime_preΨ_preΩ_of_odd` : **`#1506` scope item 2** —
  `IsCoprime (preΨₙ) (preΩₙ)`, unconditionally, at odd `n` over an algebraically closed field of
  characteristic `≠ 2`.
* `WeierstrassCurve.Affine.isCoprime_preΨ_preΩ_five_y2EqX3AddOne` : that coprimality on
  `y² = x³ + 1` over `AlgebraicClosure ℚ` at `n = 5`, so the hypothesis set is not empty.
* `WeierstrassCurve.Affine.separable_preΨ_of_wronskian_of_isAlgClosed` and
  `WeierstrassCurve.Affine.card_torsion_eq_sq_of_wronskian_identity` : `Separable (preΨₙ)` and
  `#E[n] = n²` from the Wronskian identity **alone**.

## ⚠️ What this does NOT do

* **It does not prove `#E[n] = n²`.**  `#1506` scope item 1, the Wronskian identity
  `Φₙ′·ΨSqₙ − Φₙ·ΨSqₙ′ = n·preΨₙ·preΩₙ`, is untouched and is still the whole gate.  ⚠️ Nothing in
  `EllipticCurves.Torsion.PrimaryTower` or `#293` changes, and nothing here should be read as
  saying it does: `card_torsion_eq_sq_of_wronskian_identity` carries `hid` in its signature.
* **Nothing at even `n`.**  The cleared identity holds at every `n`, but dividing by `ψ_{n+4}`
  needs `d` odd, which is what `n` odd supplies; at `d = 4` the divisor genuinely vanishes.  The
  consumer, `card_torsion_eq_sq_iff_separable_preΨ`, is odd-`n` only in any case.
* **Nothing in characteristic `2`.**  `ψ₂ ≠ 0` is the running hypothesis of the order dictionary.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and Exercise 3.7.
* M. Ward, *Memoir on elliptic divisibility sequences*, Amer. J. Math. **70** (1948).
-/

open Polynomial Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-! ## The cleared identity -/

/-- **The `Ωₙ`-pair identity, cleared of its divisors.**  At a point where `ψₙ` vanishes,

```
ψ_{n+4} · ψ₃² · (ψ_{n+2}·ψ_{n−1}² + ψ_{n−2}·ψ_{n+1}²) = 0 .
```

⚠️ No hypothesis on `n`, on the characteristic, or on the point beyond `ψₙ(x, y) = 0`; in
particular `n` ranges over `ℤ` and both parities.

The proof is three instances of `WeierstrassCurve.Affine.ψ_shift_symm_of_ψ_eq_zero` at `d = n` and
nothing else — `(m, k) = (3, 1)`, `(1, 2)` and `(1, 3)`:

```
ψ_{n+4}·ψ_{n+2}·ψ₃² = ψ₄·ψ₂·ψ_{n+3}² ,   ψ_{n+3}·ψ_{n−1} = −ψ₃·ψ_{n+1}² ,
ψ_{n+4}·ψ_{n−2} = −ψ₄·ψ₂·ψ_{n+1}² ,
```

whose combination `−R(1,3) + R(3,1) + 2·R(1,2)` is the unique small `ℤ`-relation that pins the sign
of the pair.  ⚠️ Any combination with an even coefficient on the target — and the obvious ones all
have one — proves only the squared form `(ψ_{n+2}ψ_{n−1}²)² = (ψ_{n−2}ψ_{n+1}²)²`, which is
strictly weaker and is *not* what `hpair` needs. -/
theorem ψ_pair_mul_of_ψ_eq_zero {n : ℤ} (hz : (W.ψ n).evalEval x y = 0) :
    (W.ψ (n + 4)).evalEval x y * (W.ψ 3).evalEval x y ^ 2 *
        ((W.ψ (n + 2)).evalEval x y * (W.ψ (n - 1)).evalEval x y ^ 2 +
          (W.ψ (n - 2)).evalEval x y * (W.ψ (n + 1)).evalEval x y ^ 2) = 0 := by
  have E1 := ψ_shift_symm_of_ψ_eq_zero hz 3 1
  rw [show (3 : ℤ) + 1 + n = n + 4 by ring, show (3 : ℤ) - 1 + n = n + 2 by ring,
    show (3 : ℤ) + 1 = 4 by norm_num, show (3 : ℤ) - 1 = 2 by norm_num,
    show (3 : ℤ) + n = n + 3 by ring] at E1
  have E2 := ψ_shift_symm_of_ψ_eq_zero hz 1 2
  rw [show (1 : ℤ) + 2 + n = n + 3 by ring, show (1 : ℤ) - 2 + n = n - 1 by ring,
    show (1 : ℤ) + 2 = 3 by norm_num, show (1 : ℤ) - 2 = -1 by norm_num,
    show (1 : ℤ) + n = n + 1 by ring, ψ_one_evalEval,
    show (-1 : ℤ) = -(1 : ℤ) by norm_num, ψ_neg, evalEval_neg, ψ_one_evalEval] at E2
  have E3 := ψ_shift_symm_of_ψ_eq_zero hz 1 3
  rw [show (1 : ℤ) + 3 + n = n + 4 by ring, show (1 : ℤ) - 3 + n = n - 2 by ring,
    show (1 : ℤ) + 3 = 4 by norm_num, show (1 : ℤ) - 3 = -2 by norm_num,
    show (1 : ℤ) + n = n + 1 by ring, ψ_one_evalEval,
    show (-2 : ℤ) = -(2 : ℤ) by norm_num, ψ_neg, evalEval_neg] at E3
  linear_combination ((W.ψ (n - 1)).evalEval x y ^ 2) * E1 +
    ((W.ψ 3).evalEval x y ^ 2 * (W.ψ (n + 1)).evalEval x y ^ 2) * E3 +
    ((W.ψ 4).evalEval x y * (W.ψ 2).evalEval x y *
      ((W.ψ (n - 1)).evalEval x y * (W.ψ (n + 3)).evalEval x y -
        (W.ψ 3).evalEval x y * (W.ψ (n + 1)).evalEval x y ^ 2)) * E2

/-! ## The exceptional order, `d = 3` -/

/-- At a point of order `3`, `ψ_{3j+2}³ = ψ₂^{6j+3}·ψ_{3j+1}³`.

The induction step is two applications of the quasi-periodicity
`WeierstrassCurve.Affine.ψ_add_three_evalEval_of_ψ_three_eq_zero`, which turn both sides into
`−ψ₂^{24j+24}·ψ_{3j+1}³`. -/
private lemma ψ_cube_of_ψ_three_eq_zero (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y ≠ 0) (h3 : (W.ψ 3).evalEval x y = 0) (j : ℕ) :
    (W.ψ ((3 * j + 2 : ℕ) : ℤ)).evalEval x y ^ 3 =
      (W.ψ 2).evalEval x y ^ (6 * j + 3) * (W.ψ ((3 * j + 1 : ℕ) : ℤ)).evalEval x y ^ 3 := by
  induction j with
  | zero =>
    rw [show ((3 * 0 + 2 : ℕ) : ℤ) = 2 by norm_num,
      show ((3 * 0 + 1 : ℕ) : ℤ) = 1 by norm_num, ψ_one_evalEval]
    ring
  | succ j ih =>
    have ha := ψ_add_three_evalEval_of_ψ_three_eq_zero h2 hns ht h3 (3 * j + 2)
    have hb := ψ_add_three_evalEval_of_ψ_three_eq_zero h2 hns ht h3 (3 * j + 1)
    rw [show ((3 * (j + 1) + 2 : ℕ) : ℤ) = ((3 * j + 2 : ℕ) : ℤ) + 3 by push_cast; ring,
      show ((3 * (j + 1) + 1 : ℕ) : ℤ) = ((3 * j + 1 : ℕ) : ℤ) + 3 by push_cast; ring, ha, hb]
    linear_combination (-((W.ψ 2).evalEval x y ^ (18 * j + 21))) * ih

/-- `hpair` at a point of order `3`, where every index of the shape `n + 3ℤ` is available and the
Ward route is not. -/
private lemma ψ_pair_of_ψ_three_eq_zero (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y ≠ 0) (h3 : (W.ψ 3).evalEval x y = 0) (j : ℕ) :
    (W.ψ (((3 * j + 3 : ℕ) : ℤ) + 2)).evalEval x y *
        (W.ψ (((3 * j + 3 : ℕ) : ℤ) - 1)).evalEval x y ^ 2 =
      -((W.ψ (((3 * j + 3 : ℕ) : ℤ) - 2)).evalEval x y *
        (W.ψ (((3 * j + 3 : ℕ) : ℤ) + 1)).evalEval x y ^ 2) := by
  have ha := ψ_add_three_evalEval_of_ψ_three_eq_zero h2 hns ht h3 (3 * j + 2)
  have hb := ψ_add_three_evalEval_of_ψ_three_eq_zero h2 hns ht h3 (3 * j + 1)
  rw [show ((3 * j + 3 : ℕ) : ℤ) + 2 = ((3 * j + 2 : ℕ) : ℤ) + 3 by push_cast; ring,
    show ((3 * j + 3 : ℕ) : ℤ) - 1 = ((3 * j + 2 : ℕ) : ℤ) by push_cast; ring,
    show ((3 * j + 3 : ℕ) : ℤ) + 1 = ((3 * j + 1 : ℕ) : ℤ) + 3 by push_cast; ring,
    show ((3 * j + 3 : ℕ) : ℤ) - 2 = ((3 * j + 1 : ℕ) : ℤ) by push_cast; ring, ha, hb]
  linear_combination (-((W.ψ 2).evalEval x y ^ (6 * j + 7))) *
    ψ_cube_of_ψ_three_eq_zero h2 hns ht h3 j

/-! ## `hpair` -/

/-- **`hpair`: the two summands of `Ωₙ` are negatives of one another at a point where `ψₙ`
vanishes**, at odd `n`.

⚠️ The odd-`n` hypothesis is spent only on the order `d` of the point: `d ∣ n` makes `d` odd, hence
`d ∤ 4`, hence `ψ_{n+4} ≠ 0`.  The two branches are `d = 3` — where the divisor `ψ₃` of
`WeierstrassCurve.Affine.ψ_pair_mul_of_ψ_eq_zero` vanishes and the curve-specific quasi-periodicity
takes over — and `d ≥ 5`, where the cleared identity divides. -/
theorem ψ_pair_of_ψ_eq_zero (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y ≠ 0) {n : ℕ} (hodd : Odd n)
    (hz : (W.ψ (n : ℤ)).evalEval x y = 0) :
    (W.ψ ((n : ℤ) + 2)).evalEval x y * (W.ψ ((n : ℤ) - 1)).evalEval x y ^ 2 =
      -((W.ψ ((n : ℤ) - 2)).evalEval x y * (W.ψ ((n : ℤ) + 1)).evalEval x y ^ 2) := by
  obtain ⟨e, hd0, hmin⟩ := exists_minimal_ψ_evalEval_eq_zero ht ⟨n, hodd.pos, hz⟩
  have hnz := ψ_evalEval_ne_zero_of_not_dvd h2 hns ht hd0 hmin
  have hdvd : (e + 3) ∣ n := by
    by_contra hc
    exact hnz n hc hz
  have hoddd : Odd (e + 3) := by
    obtain ⟨m, hm⟩ := hdvd
    rw [hm, Nat.odd_mul] at hodd
    exact hodd.1
  have he : e % 2 = 0 := by obtain ⟨t, htt⟩ := hoddd; omega
  rcases Nat.eq_zero_or_pos e with rfl | hepos
  · -- the least vanishing index is `3`
    obtain ⟨j, rfl⟩ : ∃ j, n = 3 * j + 3 := by
      obtain ⟨m, hm⟩ := hdvd
      exact ⟨m - 1, by have := hodd.pos; omega⟩
    exact ψ_pair_of_ψ_three_eq_zero h2 hns ht (by simpa using hd0) j
  · -- the least vanishing index is odd and at least `5`, so `ψ₃` and `ψ_{n+4}` are units
    have hp3 : (W.ψ 3).evalEval x y ≠ 0 := hmin 3 (by norm_num) (by omega)
    have hp4 : (W.ψ ((n : ℤ) + 4)).evalEval x y ≠ 0 := by
      have hnd : ¬ (e + 3) ∣ (n + 4) := by
        intro hc
        have h4 : (e + 3) ∣ 4 := (Nat.dvd_add_right hdvd).mp hc
        have := Nat.le_of_dvd (by norm_num) h4
        omega
      have := hnz (n + 4) hnd
      rwa [show (((n + 4 : ℕ)) : ℤ) = (n : ℤ) + 4 by push_cast; ring] at this
    rcases mul_eq_zero.mp (ψ_pair_mul_of_ψ_eq_zero hz) with hc | hc
    · exact absurd hc (mul_ne_zero hp4 (pow_ne_zero 2 hp3))
    · linear_combination hc

/-- **`hpair` in the shape `EllipticCurves.Torsion.WronskianSeparable` asks for.**

The two side conditions of `WeierstrassCurve.Affine.ψ_pair_of_ψ_eq_zero` are discharged here:
nonsingularity by `WeierstrassCurve.Affine.equation_iff_nonsingular` on an elliptic curve, and
`ψ₂(x, y) ≠ 0` by `WeierstrassCurve.Affine.eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero`, since
`ψₙ(x, y) = 0` at odd `n` forces `preΨₙ(x) = 0`. -/
theorem ψ_pair_of_equation [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hodd : Odd n) (x y : F) (hxy : W.Equation x y) (hz : (W.ψ (n : ℤ)).evalEval x y = 0) :
    (W.ψ ((n : ℤ) + 2)).evalEval x y * (W.ψ ((n : ℤ) - 1)).evalEval x y ^ 2 =
      -((W.ψ ((n : ℤ) - 2)).evalEval x y * (W.ψ ((n : ℤ) + 1)).evalEval x y ^ 2) := by
  have hpre : (W.preΨ (n : ℤ)).eval x = 0 := by
    refine pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ?_
    rw [← eval_pow, ← ΨSq_natCast_eq_sq_of_odd hodd, ← ψ_sq_evalEval hxy, hz]
    ring
  have hΨ₂ : W.Ψ₂Sq.eval x ≠ 0 := eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero h2 hodd hpre
  have ht : (W.ψ 2).evalEval x y ≠ 0 := fun hc => hΨ₂ (by
    rw [← ΨSq_two, ← ψ_sq_evalEval hxy, hc]; ring)
  exact ψ_pair_of_ψ_eq_zero h2 (equation_iff_nonsingular.mp hxy) ht hodd hz

/-! ## What `#1506` owed, and what is left -/

/-- **`#1506` scope item 2, discharged**: `IsCoprime (preΨₙ) (preΩₙ)` at odd `n`, over an
algebraically closed field of characteristic `≠ 2`, with no hypothesis left over.

This is `WeierstrassCurve.Affine.isCoprime_preΨ_preΩ` with its `hpair` supplied. -/
theorem isCoprime_preΨ_preΩ_of_odd [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hodd : Odd n) : IsCoprime (W.preΨ (n : ℤ)) (W.preΩ (n : ℤ)) :=
  isCoprime_preΨ_preΩ h2 hodd hodd.pos.ne' fun _ _ hxy hz => ψ_pair_of_equation h2 hodd _ _ hxy hz

/-- **Non-vacuity certificate** for the theorem above: the hypotheses
`[IsAlgClosed F] [W.IsElliptic] (2 : F) ≠ 0` and `Odd n` are jointly satisfiable, and the
coprimality really does hold somewhere.  `y² = x³ + 1` over `AlgebraicClosure ℚ` at `n = 5` — the
same curve and index `EllipticCurves.Torsion.XSupport` uses for its own certificates. -/
theorem isCoprime_preΨ_preΩ_five_y2EqX3AddOne :
    IsCoprime ((EllipticCurves.Fixture.y2EqX3AddOne (AlgebraicClosure ℚ)).preΨ ((5 : ℕ) : ℤ))
      ((EllipticCurves.Fixture.y2EqX3AddOne (AlgebraicClosure ℚ)).preΩ ((5 : ℕ) : ℤ)) :=
  isCoprime_preΨ_preΩ_of_odd (by norm_num) ⟨2, by norm_num⟩

/-- **`Separable (preΨₙ)` from the Wronskian identity alone**, at odd `n` over an algebraically
closed field of characteristic `≠ 2` with `char F ∤ n`. -/
theorem separable_preΨ_of_wronskian_of_isAlgClosed [IsAlgClosed F] [W.IsElliptic]
    (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n) (hn : (n : F) ≠ 0)
    (hid : derivative (W.Φ (n : ℤ)) * W.ΨSq (n : ℤ) -
        W.Φ (n : ℤ) * derivative (W.ΨSq (n : ℤ)) =
      (n : F[X]) * W.preΨ (n : ℤ) * W.preΩ (n : ℤ)) :
    (W.preΨ (n : ℤ)).Separable :=
  separable_preΨ_of_wronskian hodd hn hid (isCoprime_preΨ_preΩ_of_odd h2 hodd)

/-- **`#E[n] = n²` at odd `n`, from the Wronskian identity and nothing else.**

⚠️ This is still not a proof of its conclusion: `hid` is `#1506` scope item 1 and is open.  What
has changed is that it is now the *only* hypothesis — the companion `hpair` of
`WeierstrassCurve.Affine.card_torsion_eq_sq_of_wronskian_of_pair` is discharged above.  ⚠️
`EllipticCurves.Torsion.PrimaryTower`'s gate list and `#293` are therefore unchanged. -/
theorem card_torsion_eq_sq_of_wronskian_identity [DecidableEq F] [IsAlgClosed F] [W.IsElliptic]
    (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n) (hn : (n : F) ≠ 0)
    (hid : derivative (W.Φ (n : ℤ)) * W.ΨSq (n : ℤ) -
        W.Φ (n : ℤ) * derivative (W.ΨSq (n : ℤ)) =
      (n : F[X]) * W.preΨ (n : ℤ) * W.preΩ (n : ℤ)) :
    Nat.card (W.torsion n) = n ^ 2 :=
  card_torsion_eq_sq_of_wronskian h2 hodd hn hid (isCoprime_preΨ_preΩ_of_odd h2 hodd)

end WeierstrassCurve.Affine
