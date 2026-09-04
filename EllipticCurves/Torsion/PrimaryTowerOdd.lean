/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.OmegaChordSum
import EllipticCurves.Torsion.PrimaryTowerAlgClosed

/-!
# The `p`-primary tower at an odd `p`, with no hypothesis left, and `E[n] ≃+ (ℤ/nℤ)²` at odd `n`

`EllipticCurves.Torsion.PrimaryTower` runs the `p`-primary ascent once at a general index from two
hypotheses, and `EllipticCurves.Torsion.PrimaryTowerAlgClosed` discharged the first of them at every
index:

1. `hsurj : Function.Surjective fun P : W.Point => p • P` — discharged there by
   `nsmul_surjective_of_two_ne_zero`;
2. `hcard : Nat.card (W.torsion p) = p ^ 2` — **the gate**, witnessed until now only at `p = 2` and
   `p = 3`.

`EllipticCurves.Torsion.OmegaChordSum`'s `WeierstrassCurve.Affine.card_torsion_eq_sq_of_odd` proves
`#E[n] = n²` at every odd `n` over an algebraically closed field with `(2 : F) ≠ 0` and
`(n : F) ≠ 0`.  **Every odd `p` — in particular every prime `p ≥ 5` — is therefore in range, and
this file substitutes it.**  The tower is unconditional at odd `p`; nothing below carries `hcard`.

## What is actually new here, and what is only bookkeeping

⚠️ The four `_of_odd` statements in the first section are `PrimaryTowerAlgClosed`'s `_of_card`
statements with `hcard` supplied, and nothing more: **no proof below reopens the tower.**

The second section is the one place where a step is taken rather than an argument re-applied.
`AddCommGroup.equiv_zmod_sq_of_card_sq` (`EllipticCurves.Torsion.AbelianStructure`) needs, besides
the count, a **rank bound** `#A[q] ≤ q²` at every prime `q`.  `nonempty_torsionPow_addEquiv`
(`EllipticCurves.Torsion.PrimaryTower`) already discharges it at `A = E[pᵏ]` by a two-branch
argument, and both branches transfer verbatim to `A = E[n]` at an arbitrary odd `n`:

* `q ∣ n` — an element of `E[n]` killed by `q` **is** a point of `E[q]`, so `#E[n][q] ≤ #E[q]`, and
  `#E[q] = q²` is `card_torsion_eq_sq_of_odd` at `q`.  ⚠️ This is exactly the input that did not
  exist before: `q ∣ n` with `n` odd forces `q` odd, and `q ∣ n` with `(n : F) ≠ 0` forces
  `(q : F) ≠ 0`, so `card_torsion_eq_sq_of_odd` applies at `q` with no further hypothesis.
* `¬ q ∣ n` — then `Nat.Coprime q n`, and an element killed by both `q` and `n` is killed by `1`.

So the rank bound at odd `n` is a **consequence** of `card_torsion_eq_sq_of_odd`, not a separate
gate.  ⚠️ `#293`'s body records the rank bound as a second input still owed alongside `#E[n] = n²`;
at odd `n` that reading is superseded by `nonempty_torsion_addEquiv_of_odd` below.  **It does not
stand at even `n` either**, and `#293` is closed: `EllipticCurves.Torsion.StructureGeneral` reaches
every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0` by a different route — see the last section.

⚠️ Note also that `nonempty_torsion_addEquiv_of_odd` asks **no primality** of `n` and subsumes
`nonempty_torsionPow_addEquiv_of_odd` at every odd prime power, `pᵏ` being odd whenever `p` is.  The
primary-tower forms are kept because they are what `PrimaryTower`'s gate list is about and what its
consumers take; they are not a weaker route to the same place, they are the same place reached
through the tower.

## ⚠️ What this does NOT do

* **Nothing at even `n`.**  `card_torsion_eq_sq_of_odd` inherits the odd-`n` range of
  `card_torsion_eq_sq_of_wronskian_identity` exactly, so `p = 2`, the `2`-primary tower and every
  even index are untouched *here*.  ⚠️ That is a statement about this file and not about the tree:
  they are **not** left at what `EllipticCurves.Torsion.TwoPrimary` makes them.
  `EllipticCurves.Torsion.StructureGeneral` covers every even `n` with `(n : F) ≠ 0` by splitting
  `n = 2^a · m` and multiplying `TwoPrimary`'s count by the odd one.
* **It does not remove `(2 : F) ≠ 0` or `[IsAlgClosed F]`.**  Both are spent by the inputs — the
  first by `nsmul_surjective_of_two_ne_zero` *and* by `card_torsion_eq_sq_of_odd`, the second by
  both as well.
* **It does not close `#293`, but `#293` is closed.**  `#293` is the structure theorem at a general
  `n`; what is settled here is its odd half, and
  `EllipticCurves.Torsion.StructureGeneral`'s `nonempty_torsion_addEquiv` settles the whole of it at
  every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`.  ⚠️ Neither file imports the other's headline, and
  at odd `n` the
  two **assemblies** are independent: this one feeds the count and
  `card_nsmul_eq_zero_torsion_le_of_odd` straight into `AddCommGroup.equiv_zmod_sq_of_card_sq`,
  that one runs `PrimaryTower` at each prime power and glues along `Nat.recOnPosPrimePosCoprime`.
  The two agreeing is a genuine cross-check on the assembly — though not on the input, since both
  spend the same `card_torsion_eq_sq_of_odd`.

## Main statements

Every public declaration of this file is listed: **6 public, 2 private** (`exampleTwoOdd`,
`exampleFive`, the two field certificates the non-vacuity `example`s at the bottom use).

⚠️ **Every statement below takes `(2 : F) ≠ 0`, and every one takes the non-vanishing of its own
index in `F`** — `(p : F) ≠ 0` on the four `pᵏ` rows, `(n : F) ≠ 0` on the last two.  The bullets
give the conclusions and the parity of the index, and are read against this sentence for those
two.

* `WeierstrassCurve.Affine.card_torsion_pow_of_odd` : `#E[pᵏ] = (pᵏ)²` at odd `p`, no `hcard`.
* `WeierstrassCurve.Affine.finite_torsion_pow_of_odd` : `E[pᵏ]` is finite, at odd `p`.
* `WeierstrassCurve.Affine.card_torsion_pow_mul_self_of_odd` : the same count as `pᵏ · pᵏ`, the
  shape the `PrimaryBasis` and `TateModule` consumers take it in.
* **`WeierstrassCurve.Affine.nonempty_torsionPow_addEquiv_of_odd`** : `E[pᵏ] ≃+ (ℤ/pᵏℤ)²` at an odd
  prime `p` — `EllipticCurves.Torsion.PrimaryTower`'s headline with its last gate discharged.
* `WeierstrassCurve.Affine.card_nsmul_eq_zero_torsion_le_of_odd` : the rank bound `#E[n][q] ≤ q²` at
  every prime `q`, for odd `n`.
* **`WeierstrassCurve.Affine.nonempty_torsion_addEquiv_of_odd`** : `E[n] ≃+ (ℤ/nℤ)²` at **every**
  odd `n` with `(n : F) ≠ 0`, prime or not.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6, Corollary 6.4.
-/

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} [IsAlgClosed F] [W.IsElliptic]

/-! ## The `p`-primary tower at an odd `p`: `PrimaryTowerAlgClosed` with `hcard` supplied -/

/-- **`#E[pᵏ] = (pᵏ)²` with `(2 : F) ≠ 0`, at an odd `p` with `(p : F) ≠ 0`, and with no
`hcard`.**  `card_torsion_pow_of_card` (`EllipticCurves.Torsion.PrimaryTowerAlgClosed`) with its
`hcard` discharged by `card_torsion_eq_sq_of_odd`.  ⚠️ No primality: like the counting half of
`EllipticCurves.Torsion.PrimaryTower`, this asks of `p` only that it be odd and nonzero in `F`. -/
theorem card_torsion_pow_of_odd (h2 : (2 : F) ≠ 0) {p : ℕ} (hodd : Odd p) (hp : (p : F) ≠ 0)
    (k : ℕ) : Nat.card (W.torsion (p ^ k)) = (p ^ k) ^ 2 :=
  card_torsion_pow_of_card h2 (fun h => hp (by rw [h, Nat.cast_zero]))
    (card_torsion_eq_sq_of_odd h2 hodd hp) k

/-- **`E[pᵏ]` is finite** with `(2 : F) ≠ 0`, at an odd `p` with `(p : F) ≠ 0`, read off the
count. -/
theorem finite_torsion_pow_of_odd (h2 : (2 : F) ≠ 0) {p : ℕ} (hodd : Odd p) (hp : (p : F) ≠ 0)
    (k : ℕ) : Finite (W.torsion (p ^ k)) :=
  finite_torsion_pow_of_card h2 (fun h => hp (by rw [h, Nat.cast_zero]))
    (card_torsion_eq_sq_of_odd h2 hodd hp) k

/-- **`#E[pᵏ] = pᵏ · pᵏ`** with `(2 : F) ≠ 0`, at an odd `p` with `(p : F) ≠ 0` — the same count
in the shape the `PrimaryBasis` and `TateModule` consumers take their cardinality hypothesis in. -/
theorem card_torsion_pow_mul_self_of_odd (h2 : (2 : F) ≠ 0) {p : ℕ} (hodd : Odd p)
    (hp : (p : F) ≠ 0) (k : ℕ) : Nat.card (W.torsion (p ^ k)) = p ^ k * p ^ k :=
  card_torsion_pow_mul_self_of_card h2 (fun h => hp (by rw [h, Nat.cast_zero]))
    (card_torsion_eq_sq_of_odd h2 hodd hp) k

/-- **The structure theorem for `E[pᵏ]` at an odd prime `p`, with no hypothesis left.**

This is the signature `EllipticCurves.Torsion.PrimaryTower`'s gate list reduces to once
`card_torsion_eq_sq_of_odd` supplies `hcard`: over an algebraically closed field with `(2 : F) ≠ 0`,
at an odd prime `p` with `(p : F) ≠ 0`, the `p`-primary half of `E[n] ≅ (ℤ/nℤ)²` is owed nothing
further.  Every prime `p ≥ 5` is odd, so this is precisely the range that gate list called open. -/
theorem nonempty_torsionPow_addEquiv_of_odd (h2 : (2 : F) ≠ 0) {p : ℕ} (hp : p.Prime)
    (hodd : Odd p) (hpF : (p : F) ≠ 0) (k : ℕ) :
    Nonempty (W.torsion (p ^ k) ≃+ ZMod (p ^ k) × ZMod (p ^ k)) :=
  nonempty_torsionPow_addEquiv_of_card h2 hp (card_torsion_eq_sq_of_odd h2 hodd hpF) k

/-! ## The rank bound, and the structure theorem at every odd `n` -/

/-- **The rank bound `#E[n][q] ≤ q²` at every prime `q`, for odd `n` with `(2 : F) ≠ 0` and
`(n : F) ≠ 0`** — the second hypothesis of `AddCommGroup.equiv_zmod_sq_of_card_sq`.

Both branches are `nonempty_torsionPow_addEquiv`'s, at a general `n` in place of `pᵏ`.  If `q ∣ n`
then an element of `E[n]` killed by `q` is a point of `E[q]`, and `#E[q] = q²` by
`card_torsion_eq_sq_of_odd` — applicable because `q ∣ n` forces `q` odd and `(q : F) ≠ 0`.  If
`q ∤ n` then `q` and `n` are coprime and the subgroup is trivial. -/
theorem card_nsmul_eq_zero_torsion_le_of_odd (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n)
    (hn : (n : F) ≠ 0) {q : ℕ} (hq : q.Prime) :
    Nat.card {a : W.torsion n // q • a = 0} ≤ q ^ 2 := by
  by_cases hdvd : q ∣ n
  · have hqodd : Odd q := by
      rcases Nat.even_or_odd q with he | ho
      · obtain ⟨k, rfl⟩ := hdvd
        exact absurd (he.mul_right k) (Nat.not_even_iff_odd.mpr hodd)
      · exact ho
    have hqF : (q : F) ≠ 0 := by
      intro h
      obtain ⟨k, rfl⟩ := hdvd
      exact hn (by push_cast; rw [h, zero_mul])
    haveI : Finite (W.torsion q) := finite_torsion_of_intCast_ne_zero h2 hqF
    have hinj : Function.Injective
        fun a : {a : W.torsion n // q • a = 0} => (⟨(a.1 : W.Point), by
          rw [mem_torsion_iff]
          exact congrArg Subtype.val a.2⟩ : W.torsion q) := by
      intro a b hab
      simp only [Subtype.mk.injEq] at hab
      exact Subtype.ext (Subtype.ext hab)
    calc Nat.card {a : W.torsion n // q • a = 0}
        ≤ Nat.card (W.torsion q) := Nat.card_le_card_of_injective _ hinj
      _ = q ^ 2 := card_torsion_eq_sq_of_odd h2 hqodd hqF
  · have hcop : IsCoprime (q : ℤ) (n : ℤ) := by
      have hnat : Nat.Coprime q n := (Nat.Prime.coprime_iff_not_dvd hq).mpr hdvd
      simpa using Nat.isCoprime_iff_coprime.mpr hnat
    obtain ⟨u, v, huv⟩ := hcop
    have hzero : ∀ a : W.torsion n, q • a = 0 → a = 0 := by
      intro a ha
      have hqa : (q : ℤ) • a = 0 := by
        rw [show (q : ℤ) = ((q : ℕ) : ℤ) from rfl, natCast_zsmul, ha]
      have hna : (n : ℤ) • a = 0 := by
        rw [show (n : ℤ) = ((n : ℕ) : ℤ) from rfl, natCast_zsmul]
        exact nsmul_mem_torsion a
      have h1 : (1 : ℤ) • a = 0 := by
        rw [← huv, add_smul, mul_smul, mul_smul, hqa, hna, smul_zero, smul_zero, add_zero]
      simpa using h1
    have hcard1 : Nat.card {a : W.torsion n // q • a = 0} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext ((hzero a.1 a.2).trans (hzero b.1 b.2).symm)⟩, ⟨⟨0, by simp⟩⟩⟩
    rw [hcard1]
    exact Nat.one_le_pow 2 q hq.pos

/-- **`E[n] ≃+ ℤ/nℤ × ℤ/nℤ` at every odd `n` with `(n : F) ≠ 0`**, over an algebraically closed
field with `(2 : F) ≠ 0`.

This is the odd half of the structure theorem `E[n] ≅ (ℤ/nℤ)²` (`#242`, `#293`), and it asks
**nothing of `n` beyond parity**: not primality, not a prime power, not `3`-smoothness.  The count
is `card_torsion_eq_sq_of_odd` and the rank bound is `card_nsmul_eq_zero_torsion_le_of_odd`, which
is itself a consequence of the count at the prime divisors of `n`.

⚠️ It says nothing at even `n`, and in particular does not subsume
`nonempty_torsion_addEquiv_zmod_sq_of_smooth` (`EllipticCurves.Torsion.ThreePrimary`), whose range
is the `3`-smooth indices and includes every power of `2`. -/
theorem nonempty_torsion_addEquiv_of_odd (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n)
    (hn : (n : F) ≠ 0) : Nonempty (W.torsion n ≃+ ZMod n × ZMod n) := by
  haveI : Finite (W.torsion n) := finite_torsion_of_intCast_ne_zero h2 hn
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hn (by norm_num))
  exact AddCommGroup.equiv_zmod_sq_of_card_sq hn0 (fun a => nsmul_mem_torsion a)
    (card_torsion_eq_sq_of_odd h2 hodd hn)
    (fun q hq => card_nsmul_eq_zero_torsion_le_of_odd h2 hodd hn hq)

/-! ## Non-vacuity: the first indices no earlier file could reach -/

section Nonvacuity

open EllipticCurves.Fixture

private lemma exampleTwoOdd : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleFive : (5 : AlgClosedQ) ≠ 0 := by norm_num

open Classical in
/-- **`#E[5] = 25`** for `y² + y = x³` over `ℚ̄`.  `n = 5` is the index
`EllipticCurves.Torsion.ThreePrimary` names as the first one its `3`-smooth headline does not
reach. -/
example : Nat.card (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 5) = 25 := by
  have h := card_torsion_eq_sq_of_odd (W := (y2AddYEqX3 ℚ)⁄AlgClosedQ) exampleTwoOdd
    (n := 5) (by decide) exampleFive
  norm_num at h
  exact h

open Classical in
/-- **`E[5] ≃+ ℤ/5ℤ × ℤ/5ℤ`**, the structure theorem at that index. -/
example : Nonempty ((((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 5) ≃+ ZMod 5 × ZMod 5) :=
  nonempty_torsion_addEquiv_of_odd exampleTwoOdd (by decide) exampleFive

open Classical in
/-- **`E[25] ≃+ ℤ/25ℤ × ℤ/25ℤ`**, one rung up the `5`-primary tower — the tower
`EllipticCurves.Torsion.PrimaryTower`'s gate list called open at every `p ≥ 5`. -/
example : Nonempty ((((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion (5 ^ 2)) ≃+
    ZMod (5 ^ 2) × ZMod (5 ^ 2)) :=
  nonempty_torsionPow_addEquiv_of_odd exampleTwoOdd (by decide) (by decide) exampleFive 2

open Classical in
/-- **`E[15] ≃+ ℤ/15ℤ × ℤ/15ℤ`** at a composite, non-prime-power, non-`3`-smooth index: `15 = 3 · 5`
is reached by neither `nonempty_torsion_addEquiv_zmod_sq_of_smooth` nor any primary tower. -/
example : Nonempty ((((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 15) ≃+ ZMod 15 × ZMod 15) :=
  nonempty_torsion_addEquiv_of_odd exampleTwoOdd (by decide) (by norm_num)

end Nonvacuity

end WeierstrassCurve.Affine
