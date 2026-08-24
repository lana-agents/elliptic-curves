/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.CoprimeStructure
import EllipticCurves.Torsion.Divisible
import EllipticCurves.Torsion.DoublingSurjective

/-!
# The `2`-primary tower of the torsion structure theorem

Over an algebraically closed field `F` with `(2 : F) ≠ 0`, multiplication by `2` is surjective on
`E(F̄)` (`EllipticCurves.Torsion.DoublingSurjective`) and `#E[2] = 4`
(`EllipticCurves.Torsion.TwoTorsion`). Feeding those two facts into the divisibility engine of
`EllipticCurves.Torsion.Divisible` — which says that `#A[m · n] = #A[m] · #A[n]` as soon as `[n]` is
surjective on `A` — and iterating gives the whole `2`-primary part of the structure theorem
(Silverman, *AEC*, III.6, Corollary 6.4):

```
Nat.card (W.torsion (2 ^ k)) = 4 ^ k        and        W.torsion (2 ^ k) ≃+ ZMod (2^k) × ZMod (2^k).
```

In particular `#E[4] = 16` and `E[4] ≃+ ℤ/4ℤ × ℤ/4ℤ`: the first instance of the structure theorem at
a genuine **prime power** rather than a prime, and the first place the bound
`card_torsion_four_le : #E[4] ≤ 16` of `EllipticCurves.Torsion.Multiplicative` is shown to be sharp.

Composing with the coprime gluing of `EllipticCurves.Torsion.CoprimeStructure` and the sharp `n = 3`
case of `EllipticCurves.Torsion.ThreeTorsionStructure` extends this to every index of the form
`2 ^ k * 3`, for instance `E[12] ≃+ ℤ/12ℤ × ℤ/12ℤ`.

Everything here is **independent of Ward's theorem, of the elliptic-net recurrence and of the
multiplication-by-`n` coordinate formula `x(nP) = Φₙ(x)/ΨSqₙ(x)`**, which gate the general case: the
`n = 2` instance of that formula is elementary (it is the tangent-line doubling identity) and is all
that `DoublingSurjective` needs.

## The state of `E[n] ≅ (ℤ/nℤ)²` after this file

Known exactly for `n ∈ {2 ^ k, 3, 2 ^ k * 3}`. Still open:

* `#E[p] ≤ p²` for a prime `p ≥ 5`, which needs the general coordinate formula;
* the `3`-primary tower `#E[3 ^ k] = 9 ^ k`, which needs surjectivity of `[3]`. The tangent-line
  shortcut that makes `[2]` elementary is special to doubling; `[3]` genuinely needs
  `x(3P) = Φ₃/Ψ₃²`.

⚠️ **The second bullet is no longer open, and only its "still open" status was ever wrong.** Both of
its other clauses are true and stay true: `[3]` does genuinely need `x(3P) = Φ₃/Ψ₃²`, and the
tangent-line shortcut is special to doubling. That formula was proved the day after this file, in
`EllipticCurves.Torsion.TriplingSurjective`, and `EllipticCurves.Torsion.ThreePrimary` now builds
the `3`-primary tower on it and glues the two towers, giving `E[n] ≅ (ℤ/nℤ)²` for **every**
`3`-smooth `n`. The first bullet is untouched and the first open index is still `n = 5`.

## Main statements

* `WeierstrassCurve.Affine.card_torsion_mul_two`: `#E[2n] = 4 · #E[n]`.
* `WeierstrassCurve.Affine.card_torsion_two_pow`: `#E[2^k] = 4^k`.
* `WeierstrassCurve.Affine.nonempty_torsionTwoPow_addEquiv`: `E[2^k] ≃+ (ℤ/2^kℤ)²`.
* `WeierstrassCurve.Affine.card_torsion_four`, `…nonempty_torsionFour_addEquiv`: `#E[4] = 16` and
  `E[4] ≃+ (ℤ/4ℤ)²`.
* `WeierstrassCurve.Affine.nonempty_torsionTwoPowMulThree_addEquiv`: `E[2^k · 3] ≃+ (ℤ/2^k·3ℤ)²`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6, Corollary 6.4.
-/

open scoped AddSubgroup

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

variable [IsAlgClosed F] [W.IsElliptic]

/-! ## The tower `#E[2^k] = 4^k` -/

/-- Multiplication by `2` on `W.Point`, with the integer scalar `(2 : ℤ)` that
`AddSubgroup.torsionBy` uses, is surjective. This is `nsmul_two_surjective` transported along
`natCast_zsmul`; it is the only bridge needed between `DoublingSurjective` and `Divisible`. -/
private lemma zsmul_two_surjective (h2 : (2 : F) ≠ 0) :
    Function.Surjective fun P : W.Point => (2 : ℤ) • P := by
  intro Q
  obtain ⟨P, hP⟩ := nsmul_two_surjective h2 Q
  refine ⟨P, ?_⟩
  change (2 : ℤ) • P = Q
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, natCast_zsmul]
  exact hP

/-- **`#E[2n] = 4 · #E[n]`.** Multiplication by `2` is a surjection `E[2n] → E[n]` with kernel
`E[2]`, and `#E[2] = 4`.

Note that **no coprimality is assumed**. `EllipticCurves.Torsion.Coprime` has the companion
`card_torsion_two_mul`, which is the same identity but only for **odd** `n`; the statement here
holds for every `n`, and it is precisely the even case — unreachable by coprimality — that makes the
`2`-primary tower work. -/
theorem card_torsion_mul_two (h2 : (2 : F) ≠ 0) (n : ℕ) :
    Nat.card (W.torsion (n * 2)) = 4 * Nat.card (W.torsion n) := by
  have hcast : W.torsion (n * 2) = W.Point[(n : ℤ) * (2 : ℤ)] :=
    congrArg (fun k : ℤ => W.Point[k]) (by push_cast; ring)
  rw [hcast, AddSubgroup.card_torsionBy_mul_of_surjective (n : ℤ) (zsmul_two_surjective h2),
    show W.Point[(2 : ℤ)] = W.torsion 2 from rfl, card_torsion_two h2, mul_comm]

/-- **The `2`-primary tower: `#E[2^k] = 4^k`.** By induction from `#E[1] = 1`, each step
multiplying by `#E[2] = 4`. Since `4 ^ k = (2 ^ k) ^ 2`, this says `E[2^k]` attains the bound
`#E[n] ≤ n²`. -/
theorem card_torsion_two_pow (h2 : (2 : F) ≠ 0) (k : ℕ) :
    Nat.card (W.torsion (2 ^ k)) = 4 ^ k := by
  induction k with
  | zero => simp [torsion_one]
  | succ k ih =>
    rw [pow_succ, card_torsion_mul_two h2, ih, pow_succ]
    ring

/-- `E[2^k]` is finite. This is read off the count `#E[2^k] = 4^k ≠ 0` rather than from the
`3`-smooth finiteness of `EllipticCurves.Torsion.Multiplicative`, which would drag in a spurious
hypothesis `(3 : F) ≠ 0`. -/
theorem finite_torsion_two_pow (h2 : (2 : F) ≠ 0) (k : ℕ) : Finite (W.torsion (2 ^ k)) := by
  have h : Nat.card (W.torsion (2 ^ k)) ≠ 0 := by
    rw [card_torsion_two_pow h2]
    positivity
  exact (Nat.card_ne_zero.mp h).2

/-! ## The structure of `E[2^k]` -/

/-- **The structure theorem for `E[2^k]`**: over an algebraically closed field in which `2 ≠ 0`, the
`2^k`-torsion subgroup of an elliptic curve is isomorphic to `ℤ/2^kℤ × ℤ/2^kℤ`.

This is the first case of `E[n] ≅ (ℤ/nℤ)²` at a genuine prime power. It feeds the count
`#E[2^k] = 4^k = (2^k)²` into the classification core `AddCommGroup.equiv_zmod_sq_of_card_sq`; the
rank hypothesis is checked prime by prime, using `#E[2] = 4` at `p = 2` and, for odd `p`, the fact
that an element killed by both `p` and `2^k` is killed by `1` and hence zero. -/
theorem nonempty_torsionTwoPow_addEquiv (h2 : (2 : F) ≠ 0) (k : ℕ) :
    Nonempty (W.torsion (2 ^ k) ≃+ ZMod (2 ^ k) × ZMod (2 ^ k)) := by
  haveI := finite_torsion_two_pow (W := W) h2 k
  haveI := W.finite_torsion_two h2
  have hcard : Nat.card (W.torsion (2 ^ k)) = (2 ^ k) ^ 2 := by
    rw [card_torsion_two_pow h2, ← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  refine AddCommGroup.equiv_zmod_sq_of_card_sq (by positivity : 0 < 2 ^ k)
    (fun a => nsmul_mem_torsion a) hcard ?_
  intro p hp
  rcases eq_or_ne p 2 with rfl | hp2
  · -- an element of `E[2^k]` killed by `2` is a point of `E[2]`, and `#E[2] = 4 = 2²`
    have hinj : Function.Injective
        fun a : {a : W.torsion (2 ^ k) // (2 : ℕ) • a = 0} => (⟨(a.1 : W.Point), by
          rw [mem_torsion_iff]
          exact congrArg Subtype.val a.2⟩ : W.torsion 2) := by
      intro a b hab
      simp only [Subtype.mk.injEq] at hab
      exact Subtype.ext (Subtype.ext hab)
    calc Nat.card {a : W.torsion (2 ^ k) // (2 : ℕ) • a = 0}
        ≤ Nat.card (W.torsion 2) := Nat.card_le_card_of_injective _ hinj
      _ = 2 ^ 2 := by rw [card_torsion_two h2]; norm_num
  · -- for an odd prime `p`, an element of `E[2^k]` killed by `p` is killed by `1`
    have hcop : IsCoprime (p : ℤ) ((2 : ℤ) ^ k) := by
      have hnat : Nat.Coprime p (2 ^ k) :=
        Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
      simpa using Nat.isCoprime_iff_coprime.mpr hnat
    obtain ⟨u, v, huv⟩ := hcop
    have hzero : ∀ a : W.torsion (2 ^ k), (p : ℕ) • a = 0 → a = 0 := by
      intro a ha
      have hpa : (p : ℤ) • a = 0 := by rw [show (p : ℤ) = ((p : ℕ) : ℤ) from rfl, natCast_zsmul, ha]
      have hka : ((2 : ℤ) ^ k) • a = 0 := by
        rw [show ((2 : ℤ) ^ k) = (((2 ^ k : ℕ)) : ℤ) by push_cast; ring, natCast_zsmul]
        exact nsmul_mem_torsion a
      have h1 : ((1 : ℤ)) • a = 0 := by
        rw [← huv, add_smul, mul_smul, mul_smul, hpa, hka, smul_zero, smul_zero, add_zero]
      simpa using h1
    have hcard1 : Nat.card {a : W.torsion (2 ^ k) // (p : ℕ) • a = 0} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext ((hzero a.1 a.2).trans (hzero b.1 b.2).symm)⟩,
        ⟨⟨0, by simp⟩⟩⟩
    rw [hcard1]
    exact Nat.one_le_pow 2 p hp.pos

/-! ## Named instances -/

/-- **`#E[4] = 16`**, the first sharp count at a prime power. It attains the bound
`card_torsion_four_le : #E[4] ≤ 16`. -/
theorem card_torsion_four (h2 : (2 : F) ≠ 0) : Nat.card (W.torsion 4) = 16 := by
  have h := card_torsion_two_pow (W := W) h2 2
  exact h

/-- **`E[4] ≃+ ℤ/4ℤ × ℤ/4ℤ`**, the first instance of the structure theorem at a prime power. -/
theorem nonempty_torsionFour_addEquiv (h2 : (2 : F) ≠ 0) :
    Nonempty (W.torsion 4 ≃+ ZMod 4 × ZMod 4) := by
  have h := nonempty_torsionTwoPow_addEquiv (W := W) h2 2
  exact h

/-! ## Gluing with the `3`-torsion -/

/-- **`E[2^k · 3] ≃+ (ℤ/2^k·3ℤ)²`**: the `2`-primary tower glued to the sharp `n = 3` case along the
coprime factorisation `2^k ⊥ 3`. Together with `nonempty_torsionTwoPow_addEquiv` this is the widest
slice of the structure theorem available without the multiplication-by-`n` coordinate formula.
A wider slice — every `3`-smooth `n` — is available *with* that formula at `n = 3`, and is
`EllipticCurves.Torsion.ThreePrimary`'s `nonempty_torsion_addEquiv_zmod_sq_of_smooth`. -/
theorem nonempty_torsionTwoPowMulThree_addEquiv (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (k : ℕ) :
    Nonempty (W.torsion (2 ^ k * 3) ≃+ ZMod (2 ^ k * 3) × ZMod (2 ^ k * 3)) :=
  nonempty_torsion_addEquiv_zmod_sq_of_coprime
    (Nat.Coprime.pow_left k (by decide)) (nonempty_torsionTwoPow_addEquiv h2 k)
    (nonempty_torsionThree_addEquiv h2 h3)

/-- **`#E[12] = 144`.** -/
theorem card_torsion_twelve (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nat.card (W.torsion 12) = 144 := by
  have h := card_torsion_mul (W := W) (m := 4) (n := 3) (by decide)
  rw [card_torsion_four h2, card_torsion_three h2 h3] at h
  norm_num at h
  exact h

/-- **`E[12] ≃+ ℤ/12ℤ × ℤ/12ℤ`**, the first instance of the structure theorem at an index that is
neither a prime nor a prime power. -/
theorem nonempty_torsionTwelve_addEquiv (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nonempty (W.torsion 12 ≃+ ZMod 12 × ZMod 12) := by
  have h := nonempty_torsionTwoPowMulThree_addEquiv (W := W) h2 h3 2
  exact h

end WeierstrassCurve.Affine
