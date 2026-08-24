/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.ThreeTorsionStructure
import EllipticCurves.Torsion.TriplingSurjective
import EllipticCurves.Torsion.TwoPrimary
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The `3`-primary tower, and the structure theorem for every `3`-smooth `n`

Over an algebraically closed field `F` with `(2 : F) ≠ 0` multiplication by `3` is surjective on
`E(F̄)` (`EllipticCurves.Torsion.TriplingSurjective`), and over such a field with additionally
`(3 : F) ≠ 0` the count `#E[3] = 9` is sharp
(`EllipticCurves.Torsion.ThreeTorsionStructure`). Feeding those two facts into the divisibility
engine of `EllipticCurves.Torsion.Divisible` — which says that `#A[m · n] = #A[m] · #A[n]` as soon
as `[n]` is surjective on `A` — and iterating gives the whole `3`-primary part of
the structure theorem (Silverman, *AEC*, III.6, Corollary 6.4):

```
Nat.card (W.torsion (3 ^ k)) = 9 ^ k        and        W.torsion (3 ^ k) ≃+ ZMod (3^k) × ZMod (3^k).
```

This is the exact mirror of `EllipticCurves.Torsion.TwoPrimary`, and gluing the two towers along
the coprime factorisation `2 ^ a ⊥ 3 ^ b` extends the structure theorem from the indices
`2 ^ k`, `3`, `2 ^ k · 3` known before this file to **every `3`-smooth `n`** — every `n` all of
whose prime factors are `2` or `3`. In particular `#E[9] = 81` and `E[9] ≃+ ℤ/9ℤ × ℤ/9ℤ`, which is
the first instance of the structure theorem at an *odd* prime power, and `E[36] ≃+ ℤ/36ℤ × ℤ/36ℤ`,
the first at an index divisible by two distinct prime squares.

## ⚠️ The gate this file closes had been paid for a day after it was named

`EllipticCurves.Torsion.TwoPrimary` listed the `3`-primary tower as open, and it was right to at
the time. Its bullet read, verbatim:

> the `3`-primary tower `#E[3 ^ k] = 9 ^ k`, which needs surjectivity of `[3]`. The tangent-line
> shortcut that makes `[2]` elementary is special to doubling; `[3]` genuinely needs
> `x(3P) = Φ₃/Ψ₃²`.

⚠️ **Only the clause "Still open" is false, and every other clause in that bullet is true and stays
true.** `[3]` really does need `x(3P) = Φ₃/Ψ₃²`; the tangent-line shortcut really is special to
doubling. What happened is that the route was *built*, in a different file, the following day:
`EllipticCurves.Torsion.TriplingSurjective` proves `x(3P) = Φ₃/Ψ₃²` and hence
`nsmul_three_surjective`, and even says in its own docstring that this is *"the form
`Torsion/Divisible.lean`'s `torsionSmulHom_surjective` consumes"*. Nothing then consumed it.

> **A gate can go stale by being paid, not only by being wrong.** The board's recurring defect is
> the other one — a named gate that is a claim about a route rather than about the statement — and
> the two need different detectors. This one is found by comparing the date of the sentence with
> the date of the file that discharges it, not by re-examining the mathematics.

## ⚠️ This file is *not* independent of the multiplication-by-`n` coordinate formula

`EllipticCurves.Torsion.TwoPrimary` records, correctly, that everything in it is independent of
Ward's theorem, of the elliptic-net recurrence **and** of the coordinate formula
`x(nP) = Φₙ(x)/ΨSqₙ(x)`, because the `n = 2` instance of that formula is the elementary tangent-line
identity. ⚠️ **That claim must not be carried over to this file.** The `3`-primary tower consumes
`x(3P) = Φ₃/Ψ₃²` — that is exactly what `TriplingSurjective` proves and exactly what makes `[3]`
surjective. What remains true here is weaker and worth stating precisely: Ward's theorem and the
elliptic-net recurrence are still unused, and the coordinate formula is used only at `n = 3`, where
it is available.

## ⚠️ Why coprimality cannot replace divisibility here

`EllipticCurves.Torsion.Coprime` has `card_torsion_mul : #E[mn] = #E[m] · #E[n]` for coprime `m`
and `n`, with no surjectivity hypothesis at all. It is useless for a tower: the step from `3 ^ k` to
`3 ^ (k + 1)` needs `m = 3 ^ k` and `n = 3`, and `Nat.Coprime (3 ^ k) 3` fails as soon as `k ≥ 1`
(`¬ Nat.Coprime 3 3` is `by decide`). This is the gap `EllipticCurves.Torsion.Divisible` was built
to fill, and it is why the two towers in this development are the only two indices at which a
*prime power* count is known.

## The state of `E[n] ≅ (ℤ/nℤ)²` after this file

Known exactly for **every `3`-smooth `n`** — see `card_torsion_eq_sq_of_smooth` and
`nonempty_torsion_addEquiv_zmod_sq_of_smooth`. The frontier has not moved otherwise, and the
first open index is `n = 5`:

* `#E[p] ≤ p²` for a prime `p ≥ 5` needs the general coordinate formula, which is not available;
* `[p]`-surjectivity for a prime `p ≥ 5` needs it too, so neither the bound nor the tower is within
  reach at `p = 5` by the route used here.

`T₃E ≅ ℤ₃²` is **not** delivered. `EllipticCurves.TateModule.Free` obtains `T₂E ≅ ℤ₂²` from the
*coherent* system of generating pairs of `EllipticCurves.Torsion.TwoPrimaryBasis`, and is explicit
that levelwise structure theorems are not enough: *"a family of unrelated isomorphisms says nothing
about an inverse limit"*. What is delivered below is the levelwise half at `ℓ = 3`, which is its
input and not its conclusion.

## ⚠️ Where `h3` enters, measured

`nsmul_three_surjective` carries `(2 : F) ≠ 0` and **not** `(3 : F) ≠ 0`, so the only route by
which `h3` reaches `card_torsion_three_pow` is the sharp count `#E[3] = 9`. Deleting
`card_torsion_three h2 h3` from the rewrite chain of `card_torsion_mul_three`, and changing nothing
else, leaves

```
error: unsolved goals
...
h2 : 2 ≠ 0
h3 : 3 ≠ 0
n : ℕ
hcast : W.torsion (n * 3) = W.Point[↑n * 3]
⊢ Nat.card ↥(W.torsion 3) * Nat.card ↥W.Point[↑n] = 9 * Nat.card ↥(W.torsion n)
```

The count has already *factored* — that is the divisibility engine, and it needed only `h2` — and
what is missing is precisely the value `9`. Deleting the factorisation instead leaves the unfactored
`⊢ Nat.card ↥W.Point[↑n * 3] = 9 * Nat.card ↥(W.torsion n)`, with nothing for the remaining
rewrites to match.

## Main statements

* `Nat.exists_eq_two_pow_mul_three_pow`: a nonzero `n` with every prime factor `2` or `3` is a
  `2 ^ a * 3 ^ b`.
* `WeierstrassCurve.Affine.card_torsion_mul_three`: `#E[3n] = 9 · #E[n]`.
* `WeierstrassCurve.Affine.card_torsion_three_pow`: `#E[3^k] = 9^k`.
* `WeierstrassCurve.Affine.finite_torsion_three_pow`: `E[3^k]` is finite.
* `WeierstrassCurve.Affine.nonempty_torsionThreePow_addEquiv`: `E[3^k] ≃+ (ℤ/3^kℤ)²`.
* `WeierstrassCurve.Affine.card_torsion_nine`, `…nonempty_torsionNine_addEquiv`: `#E[9] = 81` and
  `E[9] ≃+ (ℤ/9ℤ)²`.
* `WeierstrassCurve.Affine.card_torsion_two_pow_mul_three_pow`,
  `…nonempty_torsionTwoPowMulThreePow_addEquiv`: the two towers glued.
* `WeierstrassCurve.Affine.card_torsion_eq_sq_of_smooth`: `#E[n] = n²` for `3`-smooth `n`, the
  equality form of `card_torsion_le_sq_of_smooth`.
* `WeierstrassCurve.Affine.nonempty_torsion_addEquiv_zmod_sq_of_smooth`: `E[n] ≃+ (ℤ/nℤ)²` for
  `3`-smooth `n`.
* `WeierstrassCurve.Affine.card_torsion_thirtysix`, `…nonempty_torsionThirtySix_addEquiv`:
  `#E[36] = 1296` and `E[36] ≃+ (ℤ/36ℤ)²`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6, Corollary 6.4.
-/

open scoped AddSubgroup

/-! ## A `3`-smooth natural number is a `2 ^ a * 3 ^ b`

`EllipticCurves.Torsion.Multiplicative` states its `3`-smooth bound `#E[n] ≤ n²` under the
hypothesis `∀ p ∈ n.primeFactors, p = 2 ∨ p = 3`, and proves it by an induction that never needs
the explicit factorisation. Sharpening the bound does need it, because the sharp counts available
are counts of `E[2 ^ a]` and `E[3 ^ b]`. The converse direction — every prime factor of
`2 ^ a * 3 ^ b` is `2` or `3` — is the private `primeFactors_two_pow_mul_three_pow` of that file. -/

/-- **A nonzero natural number all of whose prime factors are `2` or `3` is `2 ^ a * 3 ^ b`.**
Strong induction on `n`, splitting off one prime factor at a time.

This mentions no curve and is generic arithmetic; it sits at the root, in the namespace of the
object it is about, following the placement discipline of
`EllipticCurves.TateModule.DeterminantMod`. Its natural home is `Mathlib.Data.Nat.Factorization`. -/
theorem Nat.exists_eq_two_pow_mul_three_pow :
    ∀ n : ℕ, n ≠ 0 → (∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) → ∃ a b : ℕ, n = 2 ^ a * 3 ^ b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hfac
    rcases eq_or_ne n 1 with rfl | h1
    · exact ⟨0, 0, by norm_num⟩
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
    have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, hn⟩
    obtain ⟨m, hm⟩ := hpd
    have hm0 : m ≠ 0 := by rintro rfl; simp [hm] at hn
    have hmlt : m < n := by
      rw [hm]
      exact lt_mul_iff_one_lt_left (Nat.pos_of_ne_zero hm0) |>.mpr hp.one_lt
    have hmfac : ∀ q ∈ m.primeFactors, q = 2 ∨ q = 3 := by
      intro q hq
      refine hfac q (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hq).1, ?_, hn⟩)
      exact hm ▸ (Nat.mem_primeFactors.mp hq).2.1.mul_left p
    obtain ⟨a, b, hab⟩ := ih m hmlt hm0 hmfac
    rcases hfac p hmem with rfl | rfl
    · exact ⟨a + 1, b, by rw [hm, hab]; ring⟩
    · exact ⟨a, b + 1, by rw [hm, hab]; ring⟩

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

variable [IsAlgClosed F] [W.IsElliptic]

/-! ## The tower `#E[3^k] = 9^k` -/

/-- Multiplication by `3` on `W.Point`, with the integer scalar `(3 : ℤ)` that
`AddSubgroup.torsionBy` uses, is surjective. This is `nsmul_three_surjective` transported along
`natCast_zsmul`; it is the only bridge needed between `TriplingSurjective` and `Divisible`. -/
private lemma zsmul_three_surjective (h2 : (2 : F) ≠ 0) :
    Function.Surjective fun P : W.Point => (3 : ℤ) • P := by
  intro Q
  obtain ⟨P, hP⟩ := nsmul_three_surjective h2 Q
  refine ⟨P, ?_⟩
  change (3 : ℤ) • P = Q
  rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, natCast_zsmul]
  exact hP

/-- **`#E[3n] = 9 · #E[n]`.** Multiplication by `3` is a surjection `E[3n] → E[n]` with kernel
`E[3]`, and `#E[3] = 9`.

Note that **no coprimality is assumed**, and that is the point: the tower's own step has
`m = 3 ^ k` and `n = 3`, which are not coprime for any `k ≥ 1`, so `card_torsion_mul` of
`EllipticCurves.Torsion.Coprime` cannot be used for it. ⚠️ That file's `card_torsion_two_mul` is
the `2`-analogue of this lemma restricted to **odd** `n`, and it has no `3`-analogue anywhere in the
tree; the statement here holds for every `n`, and it is precisely the case `3 ∣ n` — unreachable by
coprimality — that makes the `3`-primary tower work. -/
theorem card_torsion_mul_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (n : ℕ) :
    Nat.card (W.torsion (n * 3)) = 9 * Nat.card (W.torsion n) := by
  have hcast : W.torsion (n * 3) = W.Point[(n : ℤ) * (3 : ℤ)] :=
    congrArg (fun k : ℤ => W.Point[k]) (by push_cast; ring)
  rw [hcast, AddSubgroup.card_torsionBy_mul_of_surjective (n : ℤ) (zsmul_three_surjective h2),
    show W.Point[(3 : ℤ)] = W.torsion 3 from rfl, card_torsion_three h2 h3, mul_comm]

/-- **The `3`-primary tower: `#E[3^k] = 9^k`.** By induction from `#E[1] = 1`, each step
multiplying by `#E[3] = 9`. Since `9 ^ k = (3 ^ k) ^ 2`, this says `E[3^k]` attains the bound
`#E[n] ≤ n²`. -/
theorem card_torsion_three_pow (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (k : ℕ) :
    Nat.card (W.torsion (3 ^ k)) = 9 ^ k := by
  induction k with
  | zero => simp [torsion_one]
  | succ k ih =>
    rw [pow_succ, card_torsion_mul_three h2 h3, ih, pow_succ]
    ring

/-- `E[3^k]` is finite. This is read off the count `#E[3^k] = 9^k ≠ 0` rather than from the
`3`-smooth finiteness of `EllipticCurves.Torsion.Multiplicative`, matching how
`finite_torsion_two_pow` is obtained; here neither hypothesis is spurious, since both are already
carried by the count. -/
theorem finite_torsion_three_pow (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (k : ℕ) :
    Finite (W.torsion (3 ^ k)) := by
  have h : Nat.card (W.torsion (3 ^ k)) ≠ 0 := by
    rw [card_torsion_three_pow h2 h3]
    positivity
  exact (Nat.card_ne_zero.mp h).2

/-! ## The structure of `E[3^k]` -/

/-- **The structure theorem for `E[3^k]`**: over an algebraically closed field in which `2 ≠ 0` and
`3 ≠ 0`, the `3^k`-torsion subgroup of an elliptic curve is isomorphic to `ℤ/3^kℤ × ℤ/3^kℤ`.

The count `#E[3^k] = 9^k = (3^k)²` goes into the classification core
`AddCommGroup.equiv_zmod_sq_of_card_sq`, whose rank hypothesis is checked prime by prime.

⚠️ **The case split is the mirror image of the one in `nonempty_torsionTwoPow_addEquiv`, and it is
not symmetric.** There, `p = 2` was the counting branch and every odd `p` the coprimality branch;
here `p = 3` is the counting branch, using `#E[3] = 9`, and **every** `p ≠ 3` — including `p = 2` —
is the coprimality branch, where an element killed by both `p` and `3 ^ k` is killed by `1`. -/
theorem nonempty_torsionThreePow_addEquiv (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (k : ℕ) :
    Nonempty (W.torsion (3 ^ k) ≃+ ZMod (3 ^ k) × ZMod (3 ^ k)) := by
  haveI := finite_torsion_three_pow (W := W) h2 h3 k
  haveI := W.finite_torsion_three h3
  have hcard : Nat.card (W.torsion (3 ^ k)) = (3 ^ k) ^ 2 := by
    rw [card_torsion_three_pow h2 h3, ← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  refine AddCommGroup.equiv_zmod_sq_of_card_sq (by positivity : 0 < 3 ^ k)
    (fun a => nsmul_mem_torsion a) hcard ?_
  intro p hp
  rcases eq_or_ne p 3 with rfl | hp3
  · -- an element of `E[3^k]` killed by `3` is a point of `E[3]`, and `#E[3] = 9 = 3²`
    have hinj : Function.Injective
        fun a : {a : W.torsion (3 ^ k) // (3 : ℕ) • a = 0} => (⟨(a.1 : W.Point), by
          rw [mem_torsion_iff]
          exact congrArg Subtype.val a.2⟩ : W.torsion 3) := by
      intro a b hab
      simp only [Subtype.mk.injEq] at hab
      exact Subtype.ext (Subtype.ext hab)
    calc Nat.card {a : W.torsion (3 ^ k) // (3 : ℕ) • a = 0}
        ≤ Nat.card (W.torsion 3) := Nat.card_le_card_of_injective _ hinj
      _ = 3 ^ 2 := by rw [card_torsion_three h2 h3]; norm_num
  · -- for a prime `p ≠ 3`, an element of `E[3^k]` killed by `p` is killed by `1`
    have hcop : IsCoprime (p : ℤ) ((3 : ℤ) ^ k) := by
      have hnat : Nat.Coprime p (3 ^ k) :=
        Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_three).mpr hp3)
      simpa using Nat.isCoprime_iff_coprime.mpr hnat
    obtain ⟨u, v, huv⟩ := hcop
    have hzero : ∀ a : W.torsion (3 ^ k), (p : ℕ) • a = 0 → a = 0 := by
      intro a ha
      have hpa : (p : ℤ) • a = 0 := by rw [show (p : ℤ) = ((p : ℕ) : ℤ) from rfl, natCast_zsmul, ha]
      have hka : ((3 : ℤ) ^ k) • a = 0 := by
        rw [show ((3 : ℤ) ^ k) = (((3 ^ k : ℕ)) : ℤ) by push_cast; ring, natCast_zsmul]
        exact nsmul_mem_torsion a
      have h1 : ((1 : ℤ)) • a = 0 := by
        rw [← huv, add_smul, mul_smul, mul_smul, hpa, hka, smul_zero, smul_zero, add_zero]
      simpa using h1
    have hcard1 : Nat.card {a : W.torsion (3 ^ k) // (p : ℕ) • a = 0} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext ((hzero a.1 a.2).trans (hzero b.1 b.2).symm)⟩,
        ⟨⟨0, by simp⟩⟩⟩
    rw [hcard1]
    exact Nat.one_le_pow 2 p hp.pos

/-! ## Named instances -/

/-- **`#E[9] = 81`**, the sharp count at the first odd prime power. -/
theorem card_torsion_nine (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nat.card (W.torsion 9) = 81 := by
  have h := card_torsion_three_pow (W := W) h2 h3 2
  norm_num at h
  exact h

/-- **`E[9] ≃+ ℤ/9ℤ × ℤ/9ℤ`**, the first instance of the structure theorem at an *odd* prime
power. -/
theorem nonempty_torsionNine_addEquiv (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nonempty (W.torsion 9 ≃+ ZMod 9 × ZMod 9) := by
  have h := nonempty_torsionThreePow_addEquiv (W := W) h2 h3 2
  exact h

/-! ## Gluing the two towers -/

/-- **`#E[2^a · 3^b] = (2^a · 3^b)²`**: the two towers glued along the coprime factorisation
`2 ^ a ⊥ 3 ^ b`. This is the sharp form of
`EllipticCurves.Torsion.Multiplicative`'s `card_torsion_two_pow_mul_three_pow_le`. -/
theorem card_torsion_two_pow_mul_three_pow (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (a b : ℕ) :
    Nat.card (W.torsion (2 ^ a * 3 ^ b)) = (2 ^ a * 3 ^ b) ^ 2 := by
  rw [card_torsion_mul (Nat.Coprime.pow _ _ (by decide)), card_torsion_two_pow h2,
    card_torsion_three_pow h2 h3, mul_pow, ← pow_mul, ← pow_mul, mul_comm a 2, mul_comm b 2,
    pow_mul, pow_mul]
  norm_num

/-- **`E[2^a · 3^b] ≃+ (ℤ/2^a·3^bℤ)²`**: the two towers glued along the coprime factorisation
`2 ^ a ⊥ 3 ^ b`. Taking `b ≤ 1` recovers
`EllipticCurves.Torsion.TwoPrimary`'s `nonempty_torsionTwoPowMulThree_addEquiv`. -/
theorem nonempty_torsionTwoPowMulThreePow_addEquiv (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (a b : ℕ) :
    Nonempty (W.torsion (2 ^ a * 3 ^ b) ≃+ ZMod (2 ^ a * 3 ^ b) × ZMod (2 ^ a * 3 ^ b)) :=
  nonempty_torsion_addEquiv_zmod_sq_of_coprime (Nat.Coprime.pow _ _ (by decide))
    (nonempty_torsionTwoPow_addEquiv h2 a) (nonempty_torsionThreePow_addEquiv h2 h3 b)

/-! ## Every `3`-smooth `n` -/

/-- **`#E[n] = n²` for every `3`-smooth `n ≠ 0`.** The hypotheses are exactly those of
`EllipticCurves.Torsion.Multiplicative`'s `card_torsion_le_sq_of_smooth`, with `≤` upgraded to `=`:
the `3`-smooth bound is sharp. -/
theorem card_torsion_eq_sq_of_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) : Nat.card (W.torsion n) = n ^ 2 := by
  obtain ⟨a, b, rfl⟩ := Nat.exists_eq_two_pow_mul_three_pow n hn hfac
  exact card_torsion_two_pow_mul_three_pow h2 h3 a b

/-- **`E[n] ≃+ ℤ/nℤ × ℤ/nℤ` for every `3`-smooth `n ≠ 0`**: the widest slice of the
structure theorem `E[n] ≅ (ℤ/nℤ)²` available in this development, and the first index it does
not cover is `n = 5`. -/
theorem nonempty_torsion_addEquiv_zmod_sq_of_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) :
    Nonempty (W.torsion n ≃+ ZMod n × ZMod n) := by
  obtain ⟨a, b, rfl⟩ := Nat.exists_eq_two_pow_mul_three_pow n hn hfac
  exact nonempty_torsionTwoPowMulThreePow_addEquiv h2 h3 a b

/-- **`#E[36] = 1296`.** -/
theorem card_torsion_thirtysix (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nat.card (W.torsion 36) = 1296 := by
  have h := card_torsion_two_pow_mul_three_pow (W := W) h2 h3 2 2
  norm_num at h
  exact h

/-- **`E[36] ≃+ ℤ/36ℤ × ℤ/36ℤ`**, the first instance of the structure theorem at an index divisible
by two distinct prime *squares*. -/
theorem nonempty_torsionThirtySix_addEquiv (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nonempty (W.torsion 36 ≃+ ZMod 36 × ZMod 36) := by
  have h := nonempty_torsionTwoPowMulThreePow_addEquiv (W := W) h2 h3 2 2
  exact h

/-! ### Non-vacuity

Every statement above is an equation with a nonzero right-hand side or a `Nonempty` claim, so the
vacuity risk is in the hypotheses: `[IsAlgClosed F]`, `[W.IsElliptic]`, `(2 : F) ≠ 0` and
`(3 : F) ≠ 0` have to be simultaneously satisfiable by a curve that exists. They are, on the
standard certificate curve `y² + y = x³` over an algebraic closure of `ℚ`. -/

section Nonvacuity

/-- The curve `y² + y = x³` over `ℚ`, this development's standard `n = 3` certificate curve. -/
private noncomputable def exampleCurveThree : Affine ℚ := ⟨0, 0, 1, 0, 0⟩

/-- An algebraically closed extension of `ℚ`. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

private instance : exampleCurveThree.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurveThree, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- ⚠️ `WeierstrassCurve.baseChange` is a plain `def`, so `[(W⁄F).IsElliptic]` is **not** found by
bare `inferInstance` from `[W.IsElliptic]`; this is the idiom
`EllipticCurves.TateModule.Determinant` documents for exactly that reason. -/
private instance : (exampleCurveThree⁄exampleField).IsElliptic :=
  inferInstanceAs (exampleCurveThree.map (algebraMap ℚ exampleField)).IsElliptic

/-- Every prime factor of `72 = 2³ · 3²` is `2` or `3`. -/
private lemma primeFactors_seventytwo : ∀ p ∈ (72 : ℕ).primeFactors, p = 2 ∨ p = 3 := by
  intro p hp
  obtain ⟨hpp, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
  rw [show (72 : ℕ) = 2 ^ 3 * 3 ^ 2 from rfl] at hdvd
  rcases (Nat.Prime.dvd_mul hpp).mp hdvd with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp (hpp.dvd_of_dvd_pow h))

private lemma exampleTwo : (2 : exampleField) ≠ 0 := by norm_num

private lemma exampleThree : (3 : exampleField) ≠ 0 := by norm_num

open Classical in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on a curve that exists, `E[9]` really has `81` points, so
the `3`-primary tower is not a statement about an empty family of curves. -/
example : Nat.card ((exampleCurveThree⁄exampleField).torsion 9) = 81 :=
  card_torsion_nine exampleTwo exampleThree

open Classical in
/-- The structure statement at the same index, restated in full rather than projected out of an
existential. -/
example : Nonempty ((exampleCurveThree⁄exampleField).torsion 9 ≃+ ZMod 9 × ZMod 9) :=
  nonempty_torsionNine_addEquiv exampleTwo exampleThree

open Classical in
/-- The `3`-smooth headline at an index no earlier file could reach: `72 = 2³ · 3²` is neither a
prime power nor of the form `2 ^ k · 3`.

⚠️ The `3`-smoothness side condition is **not** `by decide`: the `Decidable` instance for
`∀ p ∈ Nat.primeFactors 72, p = 2 ∨ p = 3` gets stuck rather than reducing, with
`reduction got stuck at the Decidable instance List.decidableBAll …`. It is discharged by
`primeFactors_seventytwo` above instead, which is the specialisation of
`EllipticCurves.Torsion.Multiplicative`'s private `primeFactors_two_pow_mul_three_pow`. -/
example : Nat.card ((exampleCurveThree⁄exampleField).torsion 72) = 5184 := by
  have h := card_torsion_eq_sq_of_smooth (W := exampleCurveThree⁄exampleField) exampleTwo
    exampleThree (n := 72) (by norm_num) primeFactors_seventytwo
  norm_num at h
  exact h

end Nonvacuity

end WeierstrassCurve.Affine
