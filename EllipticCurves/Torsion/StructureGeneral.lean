/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.CoprimeStructure
import EllipticCurves.Torsion.OmegaChordSum

/-!
# `#E[n] = n²` and `E[n] ≅ (ℤ/nℤ)²` at every `n` prime to the characteristic

`EllipticCurves.Torsion.OmegaChordSum` proves `#E[n] = n²` at **odd** `n`
(`WeierstrassCurve.Affine.card_torsion_eq_sq_of_odd`), because its route runs through
`Separable (preΨₙ)` and `EllipticCurves.Torsion.OddTorsionCount`'s `2`-to-`1` count of the nonzero
`n`-torsion over the roots of `preΨₙ`, which is odd-`n` by construction.

**This file removes the parity restriction, and the argument is arithmetic, not geometric.**  Write
`n = 2^a · m` with `m` odd.  The two factors are coprime, `#E[2^a] = 4^a` has been on `main` since
the `2`-primary tower and was never gated on the Wronskian identity, and `#E[m] = m²` is the odd
theorem.  `EllipticCurves.Torsion.Coprime`'s `card_torsion_mul` multiplies them.  ⚠️ **Every** `n`
is `2^a · (odd)`, so this covers every index, not a wider slice of them:

```
#E[n] = n²                       for every n with (n : F) ≠ 0.
```

The structure theorem follows by the same shape one level up.  `#E[p] = p²` is now available at
**every** prime `p` with `(p : F) ≠ 0`, and `nsmul_surjective_of_two_ne_zero`
(`EllipticCurves.Torsion.TwoTorsionOrder`) has supplied surjectivity of `[p]` at every nonzero index
since PR #569 — so `EllipticCurves.Torsion.PrimaryTower`'s `nonempty_torsionPow_addEquiv` applies at
every prime power, and `EllipticCurves.Torsion.CoprimeStructure`'s
`nonempty_torsion_addEquiv_zmod_sq_of_coprime` glues the prime powers along
`Nat.recOnPosPrimePosCoprime`:

```
E[n] ≃+ ℤ/nℤ × ℤ/nℤ              for every n with (n : F) ≠ 0.
```

That is `#242`, the structure theorem for the `n`-torsion, and `#293`'s conclusion.

## Why the hypothesis is `(n : F) ≠ 0` and not `Odd n`

⚠️ `(n : F) ≠ 0` is not a convenience; it is the sharp condition, and at `p = char F` the
conclusion is **false** rather than unproved — `E[p]` is `0` or `ℤ/pℤ` there, never `(ℤ/pℤ)²`.  So a
docstring recording "the even case" as open is describing a gap that does not exist, while one
recording the characteristic case as open is correct.

## What each input contributes, so that nothing here is mistaken for new mathematics

* `WeierstrassCurve.Affine.card_torsion_eq_sq_of_odd` (`Torsion.OmegaChordSum`) — the odd count.
  This is the only deep input, and it is the whole of `#1506` item 1's payoff.
* `WeierstrassCurve.Affine.card_torsion_two_pow` (`Torsion.TwoPrimary`) — `#E[2^k] = 4^k`.
* `WeierstrassCurve.Affine.card_torsion_mul` (`Torsion.Coprime`) — `#E[mn] = #E[m]·#E[n]` at coprime
  `m`, `n`, ⚠️ **with no finiteness hypothesis**, which is what lets the count be assembled before
  finiteness is known at `n`.
* `WeierstrassCurve.Affine.nonempty_torsionPow_addEquiv` (`Torsion.PrimaryTower`) — the prime-power
  structure theorem from surjectivity and `#E[p] = p²`.  ⚠️ It is the *only* statement in that file
  that needs `p.Prime`, and this file supplies exactly the two hypotheses it was written to take.
* `WeierstrassCurve.Affine.nonempty_torsion_addEquiv_zmod_sq_of_coprime`
  (`Torsion.CoprimeStructure`) — the Chinese-remainder glue.
* `WeierstrassCurve.Affine.nsmul_surjective_of_two_ne_zero` (`Torsion.TwoTorsionOrder`) —
  surjectivity of `[n]` at every `n ≠ 0`.  ⚠️ It does **not** need `(n : F) ≠ 0`, and it has been a
  theorem since long before the count was; nothing about the `≥ n²` half follows from it.

**No new geometry, no new polynomial identity and no new curve is used below.**

## Main statements

⚠️ Every public declaration of this file is listed: **7 public, 0 private.**

* `WeierstrassCurve.Affine.card_torsion_eq_sq` : **`#E[n] = n²` at every `n` with `(n : F) ≠ 0`.**
* `WeierstrassCurve.Affine.nonempty_torsionPrimePow_addEquiv` : `E[p^k] ≃+ (ℤ/p^kℤ)²` at every
  prime `p` with `(p : F) ≠ 0`.
* `WeierstrassCurve.Affine.nonempty_torsion_addEquiv` : **`E[n] ≃+ ℤ/nℤ × ℤ/nℤ` at every `n` with
  `(n : F) ≠ 0`** — `#242`.
* `WeierstrassCurve.Affine.card_torsion_five`, `…nonempty_torsionFive_addEquiv` : the first index
  outside `{2, 3}`-smooth, which is where every previous statement of both results stopped.
* `WeierstrassCurve.Affine.card_torsion_ten`, `…nonempty_torsionTen_addEquiv` : the first **even**
  index reachable by neither the `3`-smooth statements nor the odd ones.

## ⚠️ What this does NOT do

* **Nothing at `n = 0` in `F`.**  `(n : F) ≠ 0` is a hypothesis of every statement, and in
  characteristic `p` the conclusion is false at `p ∣ n`, not merely unavailable.
* It proves **no** new identity about division polynomials and touches no file that does.
* It does not touch `EllipticCurves.Torsion.PrimaryTower`'s gate list, which is `#1522`.  ⚠️ That
  gate is `#E[p] = p²` and `card_torsion_eq_sq` discharges it at every `p` with `(p : F) ≠ 0`, but
  `PrimaryTower` is *upstream* of `EllipticCurves.Torsion.OmegaChordSum` and so cannot import this
  file; the discharge has to happen in a leaf, which is what this one is.
* `#268` (`T_ℓ E ≅ ℤ_ℓ²`) is not assembled here, though `nonempty_torsion_addEquiv` is the input it
  was waiting for at `ℓ ≥ 5`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6, Corollary 6.4.
-/

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} [IsAlgClosed F] [W.IsElliptic]

/-! ### The count -/

/-- **`#E[n] = n²` at every `n` with `(n : F) ≠ 0`**, with no parity hypothesis.

Split `n = 2^a · m` at the `2`-adic valuation: `Nat.ordProj_mul_ordCompl_eq_self` gives the
factorisation and `Nat.not_dvd_ordCompl` gives that `m` is odd, hence coprime to `2^a`.  Then
`card_torsion_mul` reduces the count to `#E[2^a] = 4^a` (`card_torsion_two_pow`, which never
depended on the Wronskian identity) and `#E[m] = m²` (`card_torsion_eq_sq_of_odd`).

⚠️ `(m : F) ≠ 0` is inherited from `(n : F) ≠ 0` rather than assumed: `m` divides `n`, so a
vanishing `m` would force a vanishing `n`.  That is the only place the hypothesis is used at the
odd factor, and it is why the statement needs `(n : F) ≠ 0` and not the stronger `n` prime to
`char F` spelled out prime by prime. -/
theorem card_torsion_eq_sq (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : (n : F) ≠ 0) :
    Nat.card (W.torsion n) = n ^ 2 := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  set a := n.factorization 2 with ha
  set m := n / 2 ^ a with hm
  have hsplit : 2 ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hdvd : ¬ (2 ∣ m) := Nat.not_dvd_ordCompl Nat.prime_two hn0
  have hcop : Nat.Coprime (2 ^ a) m :=
    Nat.Coprime.pow_left _ ((Nat.prime_two.coprime_iff_not_dvd).mpr hdvd)
  have hmF : (m : F) ≠ 0 := fun hz => hn (by rw [← hsplit]; push_cast; rw [hz, mul_zero])
  have hodd : Odd m := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hdvd)
  have hmul := card_torsion_mul (W := W) hcop
  rw [hsplit] at hmul
  rw [hmul, card_torsion_two_pow h2 a, card_torsion_eq_sq_of_odd h2 hodd hmF, ← hsplit,
    show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, mul_pow, ← pow_mul, mul_comm a 2]

/-! ### The structure theorem -/

/-- **`E[p^k] ≃+ ℤ/p^kℤ × ℤ/p^kℤ` at every prime `p` with `(p : F) ≠ 0`.**

`nonempty_torsionPow_addEquiv` (`EllipticCurves.Torsion.PrimaryTower`) takes exactly two inputs
beyond primality: surjectivity of `[p]`, which `nsmul_surjective_of_two_ne_zero` supplies at every
nonzero index, and `#E[p] = p²`, which `card_torsion_eq_sq` now supplies at every `p` with
`(p : F) ≠ 0`.  ⚠️ The general-`p` form of `nonempty_torsionTwoPow_addEquiv` and of
`nonempty_torsionThreePow_addEquiv`, and it subsumes both. -/
theorem nonempty_torsionPrimePow_addEquiv (h2 : (2 : F) ≠ 0) {p : ℕ} (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (k : ℕ) :
    Nonempty (W.torsion (p ^ k) ≃+ ZMod (p ^ k) × ZMod (p ^ k)) :=
  nonempty_torsionPow_addEquiv hp (nsmul_surjective_of_two_ne_zero h2 hp.pos.ne')
    (card_torsion_eq_sq h2 hpF) k

/-- **`E[n] ≃+ ℤ/nℤ × ℤ/nℤ` at every `n` with `(n : F) ≠ 0`** — the structure theorem for the
`n`-torsion of an elliptic curve over an algebraically closed field, `#242`.

`Nat.recOnPosPrimePosCoprime` reduces to prime powers and coprime products.  The prime-power case is
`nonempty_torsionPrimePow_addEquiv`; the coprime case is
`nonempty_torsion_addEquiv_zmod_sq_of_coprime`; `n = 0` is excluded by the hypothesis, and `n = 1`
is `nonempty_torsionTwoPow_addEquiv` at `k = 0`, which is the same trick Mathlib's own
`Nat.recOnPrimeCoprime` uses to reach `1`.

⚠️ The hypothesis `(n : F) ≠ 0` propagates in both directions of the recursion without extra work: a
divisor of `n` cannot vanish in `F` if `n` does not, and that is all either branch needs.

⚠️ This **subsumes** `nonempty_torsion_addEquiv_zmod_sq_of_smooth`
(`EllipticCurves.Torsion.ThreePrimary`), whose `3`-smooth `n ≠ 0` with `(2 : F) ≠ 0`, `(3 : F) ≠ 0`
forces `(n : F) ≠ 0`; the `example` below is the machine-checked form of that claim.  It does not
subsume anything at `p = char F`, where the conclusion is false. -/
theorem nonempty_torsion_addEquiv (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : (n : F) ≠ 0) :
    Nonempty (W.torsion n ≃+ ZMod n × ZMod n) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
      refine nonempty_torsionPrimePow_addEquiv h2 hp ?_ k
      intro hz
      exact hn (by push_cast; rw [hz]; exact zero_pow hk.ne')
  | zero => exact absurd (by push_cast; ring) hn
  | one => simpa using nonempty_torsionTwoPow_addEquiv (W := W) h2 0
  | coprime a b _ _ hcop Pa Pb =>
      have haF : (a : F) ≠ 0 := fun hz => hn (by push_cast; rw [hz, zero_mul])
      have hbF : (b : F) ≠ 0 := fun hz => hn (by push_cast; rw [hz, mul_zero])
      exact nonempty_torsion_addEquiv_zmod_sq_of_coprime hcop (Pa haF) (Pb hbF)

/-- ⚠️ The `3`-smooth statement is an instance of the general one, so no coverage is lost by
preferring it.  `n = 2^a·3^b ≠ 0` with `2 ≠ 0` and `3 ≠ 0` in `F` forces `(n : F) ≠ 0`; this is that
implication, machine-checked, and it is the reason the docstring above may claim subsumption. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) :
    Nonempty (W.torsion n ≃+ ZMod n × ZMod n) := by
  obtain ⟨a, b, rfl⟩ := Nat.exists_eq_two_pow_mul_three_pow n hn hfac
  refine nonempty_torsion_addEquiv h2 ?_
  push_cast
  exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)

/-! ### The first indices that were out of reach

⚠️ `n = 5` is where every previous statement of both results stopped — `ThreePrimary`'s
*"the first index it does not cover is `n = 5`"* — and `n = 10` is the first index reachable by
neither the `3`-smooth statements nor by the odd ones.  These are named rather than left as
`example`s so that a later reader can grep for them, and so that they are *consumed* if anything
downstream wants a concrete instance. -/

/-- **`#E[5] = 25`.** -/
theorem card_torsion_five (h2 : (2 : F) ≠ 0) (h5 : (5 : F) ≠ 0) :
    Nat.card (W.torsion 5) = 25 := by
  have h := card_torsion_eq_sq (W := W) h2 (n := 5) (by exact_mod_cast h5)
  norm_num at h
  exact h

/-- **`E[5] ≃+ ℤ/5ℤ × ℤ/5ℤ`**, the first instance of the structure theorem outside the `3`-smooth
range. -/
theorem nonempty_torsionFive_addEquiv (h2 : (2 : F) ≠ 0) (h5 : (5 : F) ≠ 0) :
    Nonempty (W.torsion 5 ≃+ ZMod 5 × ZMod 5) :=
  nonempty_torsion_addEquiv h2 (by exact_mod_cast h5)

/-- **`#E[10] = 100`**, at an index that is neither odd nor `3`-smooth. -/
theorem card_torsion_ten (h2 : (2 : F) ≠ 0) (h5 : (5 : F) ≠ 0) :
    Nat.card (W.torsion 10) = 100 := by
  have h := card_torsion_eq_sq (W := W) h2 (n := 10)
    (by rw [show ((10 : ℕ) : F) = 2 * 5 by push_cast; ring]; exact mul_ne_zero h2 h5)
  norm_num at h
  exact h

/-- **`E[10] ≃+ ℤ/10ℤ × ℤ/10ℤ`** — the first index at which the structure theorem needed both the
even and the odd half, and neither the `3`-smooth statements nor an odd-`n` statement reaches it. -/
theorem nonempty_torsionTen_addEquiv (h2 : (2 : F) ≠ 0) (h5 : (5 : F) ≠ 0) :
    Nonempty (W.torsion 10 ≃+ ZMod 10 × ZMod 10) :=
  nonempty_torsion_addEquiv h2
    (by rw [show ((10 : ℕ) : F) = 2 * 5 by push_cast; ring]; exact mul_ne_zero h2 h5)

end WeierstrassCurve.Affine
