/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.Torsion.ThreeTorsionStructure
import EllipticCurves.Torsion.TriplingSurjective
import EllipticCurves.Torsion.TwoPrimary
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The `3`-primary tower, and the structure theorem for every `3`-smooth `n`

Over an algebraically closed field `F` with `(2 : F) ≠ 0` multiplication by `3` is surjective on
`E(F̄)` (`EllipticCurves.Torsion.TriplingSurjective`), and over such a field with additionally
`(3 : F) ≠ 0` the count `#E[3] = 9` is sharp
(`EllipticCurves.Torsion.ThreeTorsionStructure`). Those two facts are exactly the input of
`EllipticCurves.Torsion.PrimaryTower`, which runs the ascent once at general `p` — through the
divisibility engine of `EllipticCurves.Torsion.Divisible`, which says that
`#A[m · n] = #A[m] · #A[n]` as soon as `[n]` is surjective on `A` — and iterating gives the whole
`3`-primary part of the structure theorem (Silverman, *AEC*, III.6, Corollary 6.4):

```
Nat.card (W.torsion (3 ^ k)) = 9 ^ k        and        W.torsion (3 ^ k) ≃+ ZMod (3^k) × ZMod (3^k).
```

⚠️ **The ascent itself is not in this file**, and neither is it in
`EllipticCurves.Torsion.TwoPrimary`: the two were the same argument with `3` for `2`, and
`EllipticCurves.Torsion.PrimaryTower` is that argument with the index erased. What is `n`-specific
here — and it is all that ever was — is the pair `nsmul_three_surjective`, `card_torsion_three`.

Gluing the two towers along the coprime factorisation `2 ^ a ⊥ 3 ^ b` extends the structure theorem
from the indices `2 ^ k`, `3`, `2 ^ k · 3` known before this file to **every `3`-smooth `n`** —
every `n` all of whose prime factors are `2` or `3`. In particular `#E[9] = 81` and
`E[9] ≃+ ℤ/9ℤ × ℤ/9ℤ`, which is the first instance of the structure theorem at an *odd* prime power,
and `E[36] ≃+ ℤ/36ℤ × ℤ/36ℤ`, the first at an index divisible by two distinct prime squares.

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
`nonempty_torsion_addEquiv_zmod_sq_of_smooth`. The frontier has not moved otherwise *by anything in
this file*.  ⚠️ This paragraph used to end *"and the first open index is `n = 5`"*, which is false
downstream: `nonempty_torsion_addEquiv_of_odd` (`EllipticCurves.Torsion.PrimaryTowerOdd`) settles
`E[n] ≃+ (ℤ/nℤ)²` at **every** odd `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`, `n = 5` included —
⚠️ **both hypotheses, and this clause used to name only the index one** (`#1137`).  What the two
smooth statements here still add is the even part: every `2 ^ k` and every `2 ^ a · 3 ^ b`, which
no odd-index theorem reaches.

⚠️ **Both reasons this paragraph used to give for that were the coordinate formula, and both
are now false.**  It read *"`#E[p] ≤ p²` … needs the general coordinate formula, which is not
available"* and *"`[p]`-surjectivity … needs it too"*.  On `main` today:

* `#E[p] ≤ p²` at every `p` is `card_torsion_le_sq` (`EllipticCurves.Torsion.XSupport`), over a
  field with `(2 : F) ≠ 0` and `(p : F) ≠ 0`;
* `[p]`-surjectivity at every nonzero index is `nsmul_surjective_of_two_ne_zero`
  (`EllipticCurves.Torsion.TwoTorsionOrder`), over `F̄` with `(2 : F) ≠ 0`;
* the coordinate formula itself is proved at every index with `(2 : F) ≠ 0`, under `ΨSqₙ(x) ≠ 0` —
  `hasXCoordFormula_of_two_ne_zero` (`EllipticCurves.Torsion.NsmulOrder`) on the `x`-half,
  `nsmul_eq_some_omegaY_of_ΨSq_ne_zero` (`EllipticCurves.Torsion.NsmulYPeriodic`) on the `y`-half.

⚠️ **The `≥` half of `#E[p] = p²` at `p ≥ 5` used to be what was open, and it no longer is.**
`EllipticCurves.Torsion.PrimaryTower` carries the authoritative gate list; the single entry it had
after PR #582 was one polynomial identity about one curve over one ring (`#1506` scope item 1,
`#1490` item 3), and that identity is `WeierstrassCurve.hasWronskianId`
(`EllipticCurves.Torsion.OmegaChordSum`).  `card_torsion_eq_sq_of_odd` is the count at every odd
`p`, and nothing in *this* file gates or supplies it.

⚠️ This paragraph used to open *"`T₃E ≅ ℤ₃²` is **not** delivered"*, and that clause is now false:
`EllipticCurves.TateModule.FreeThree` delivers it. The rest of the paragraph is still exactly
right and is what that file consumes. `EllipticCurves.TateModule.PrimaryFree` obtains
`T_ℓE ≅ ℤ_ℓ²` from a *coherent* system of generating pairs — at `ℓ = 3` the one built by
`EllipticCurves.Torsion.ThreePrimaryBasis` — and is explicit that levelwise structure theorems are
not enough: *"a family of unrelated isomorphisms says nothing about an inverse limit"*. What is
delivered below is the levelwise half at `ℓ = 3`, which is that construction's input and not its
conclusion.

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
⊢ Nat.card ↥(W.torsion 3) * Nat.card ↥(W.torsion n) = 9 * Nat.card ↥(W.torsion n)
```

The count has already *factored* — that is `card_torsion_mul_of_surjective`, and it needed only
`h2` — and what is missing is precisely the value `9`. Deleting the factorisation instead makes the
remaining rewrite fail outright, *"did not find an occurrence of the pattern
`Nat.card ↥(torsion ?m 3)`"*, there being no `W.torsion 3` in `#E[3n] = 9 · #E[n]` to rewrite.

⚠️ This measurement was re-run when the ascent moved to `EllipticCurves.Torsion.PrimaryTower`; its
conclusion is unchanged, but the goal it quotes is not the one the earlier proof produced — that one
carried a `hcast` hypothesis and displayed `W.Point[↑n]` rather than `W.torsion n`. **A quoted
compiler output is a claim about a proof that no longer exists the moment the proof is rewritten**,
and it is invisible to every other check in this tree.

## Main statements

* `Nat.exists_eq_two_pow_mul_three_pow`: a nonzero `n` with every prime factor `2` or `3` is a
  `2 ^ a * 3 ^ b`.
* `WeierstrassCurve.Affine.card_torsion_mul_three`: `#E[3n] = 9 · #E[n]`.
* `WeierstrassCurve.Affine.card_torsion_three_pow`: `#E[3^k] = 9^k`, and
  `WeierstrassCurve.Affine.card_torsion_three_pow_mul_self`, the same count written `3^k · 3^k`.
* `WeierstrassCurve.Affine.finite_torsion_three_pow`: `E[3^k]` is finite.
* `WeierstrassCurve.Affine.nonempty_torsionThreePow_addEquiv`: `E[3^k] ≃+ (ℤ/3^kℤ)²`.
* `WeierstrassCurve.Affine.card_torsion_nine`, `…nonempty_torsionNine_addEquiv`: `#E[9] = 81` and
  `E[9] ≃+ (ℤ/9ℤ)²`.
* `WeierstrassCurve.Affine.card_torsion_two_pow_mul_three_pow`,
  `…nonempty_torsionTwoPowMulThreePow_addEquiv`: the two towers glued.
* `WeierstrassCurve.Affine.card_torsion_eq_sq_of_smooth`: `#E[n] = n²` with `(2 : F) ≠ 0` and
  `(3 : F) ≠ 0`, at `3`-smooth `n ≠ 0`, the equality form of `card_torsion_le_sq_of_smooth`.
* `WeierstrassCurve.Affine.nonempty_torsion_addEquiv_zmod_sq_of_smooth`: `E[n] ≃+ (ℤ/nℤ)²` with
  `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, at `3`-smooth `n ≠ 0`.
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

/-- **A `3`-smooth `n ≠ 0` is prime to the characteristic as soon as `2` and `3` are.**

The shared home for what was, until this landed, seven byte-identical `private` copies across
`EllipticCurves/FunctionField/` — one each in `MulByNPlaceComposition`, `NthRootOfPullbackN`,
`WeilPairingAlternatingAssemblyN`, `WeilPairingAlternatingConsumerN`,
`WeilPairingDivisorSlotBilinearHprinN`, `WeilPairingGaloisRootN` and
`WeilPairingTranslationSlotHprinN`, each documented as *"a copy rather than a citation: the twin in
`MulByNPlaceComposition` is `private` there"*.  ⚠️ This file is already in the transitive import
closure of **all seven**, so the consolidation costs no import edge in any of them; that is why it
belongs here and not in a new leaf.

⚠️ Stated over a fresh field `K` rather than over a section variable, and placed above this file's
`namespace WeierstrassCurve.Affine`, so that it mentions neither a curve nor its coordinate ring:
it is generic arithmetic about a cast, exactly as `Nat.exists_eq_two_pow_mul_three_pow` above is
generic arithmetic about a factorisation.

⚠️ **This is the `((n : ℤ) : K)` form.**  The `(n : K)` form is `Nat.natCast_ne_zero_of_smooth`
immediately below, which is this one with the composite cast collapsed, and its consumer is
`EllipticCurves.TateModule.OpenKernel`.  ⚠️ This paragraph used to say that form was *"deliberately
not retired here"* because PR #601 was open against `OpenKernel`'s private copy; #601 has landed
and the copy is gone. -/
theorem Nat.intCast_ne_zero_of_smooth {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) : ((n : ℤ) : K) ≠ 0 := by
  obtain ⟨a, b, rfl⟩ := Nat.exists_eq_two_pow_mul_three_pow n hn hfac
  push_cast
  exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)

/-- **The `(n : K)` form of `Nat.intCast_ne_zero_of_smooth`**, with the same hypotheses and the
composite cast `((n : ℤ) : K)` collapsed to `(n : K)`.

Both forms are consumed in this development and neither is a restatement of the other at the
elaborator's level, which is why both are stated rather than one being left to the caller:
`EllipticCurves.TateModule.OpenKernel` takes `(n : K)` — its `finite_torsion_of_intCast_ne_zero`
route states the condition that way — and the `EllipticCurves/FunctionField/` layer takes
`((n : ℤ) : K)`.

⚠️ This retires the last of the **eight** `private` copies this pair of lemmas had grown
(`#1552`).  Seven went with `Nat.intCast_ne_zero_of_smooth` above; the eighth was
`EllipticCurves.TateModule.OpenKernel`'s `natCast_ne_zero_of_smooth`, held back only because
PR #601 was open against its proof body at the time.

⚠️ The binder shape here is the one the seven retired consumers use — `{n} (hn) (hfac)` — and
**not** `OpenKernel`'s `∀ n : ℕ, n ≠ 0 → …`.  `#1552` asked for the call site to be adapted rather
than the shared lemma bent, and it was. -/
theorem Nat.natCast_ne_zero_of_smooth {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) : (n : K) ≠ 0 := by
  simpa using Nat.intCast_ne_zero_of_smooth h2 h3 hn hfac

/-- **`10` is not `3`-smooth**, where *`3`-smooth* is this development's
`∀ p ∈ n.primeFactors, p = 2 ∨ p = 3`.

⚠️ This is a *falsifier*, and it is what makes an `n = 10` non-vacuity certificate say more than an
`n = 4` or `n = 6` one: `4` and `6` are `3`-smooth, so a certificate at either is equally a
certificate for the `_of_smooth` headline it sits under, and a *"general"* statement reaching only
`{2, 3}`-indices would pass it unchanged.  `10 = 2 · 5` is even and not `3`-smooth, so no
`_of_smooth` statement can be instantiated there at any hypotheses.

⚠️ **Proved, not `decide`d.**  The `Decidable` instance for a bounded quantifier over
`Nat.primeFactors` gets stuck (`#1213`), which is the same trap `primeFactors_four` and
`smoothTwelve` document elsewhere on this board.

Shared rather than copied for the reason `Nat.intCast_ne_zero_of_smooth` above is: three
`FunctionField/` files certify at `n = 10` and this file is already in the import closure of all
three. -/
theorem Nat.ten_not_smooth : ¬ (∀ p ∈ (10 : ℕ).primeFactors, p = 2 ∨ p = 3) := by
  intro hfac
  have h5 : (5 : ℕ) ∈ (10 : ℕ).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_five, ⟨2, by norm_num⟩, by norm_num⟩
  rcases hfac 5 h5 with h | h <;> omega

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

variable [IsAlgClosed F] [W.IsElliptic]

/-! ## The tower `#E[3^k] = 9^k`

⚠️ **The tower itself is not built here.** `EllipticCurves.Torsion.PrimaryTower` climbs it once at
general `p`, from surjectivity of `[p]` and the count `#E[p] = p²`; this file supplies those two at
`p = 3`, as `nsmul_three_surjective` and `card_torsion_three`, and everything below is an
instance. -/

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
  rw [card_torsion_mul_of_surjective (nsmul_three_surjective h2) n, card_torsion_three h2 h3]

/-- **The `3`-primary tower: `#E[3^k] = 9^k`.** By induction from `#E[1] = 1`, each step
multiplying by `#E[3] = 9`. Since `9 ^ k = (3 ^ k) ^ 2`, this says `E[3^k]` attains the bound
`#E[n] ≤ n²`. -/
theorem card_torsion_three_pow (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (k : ℕ) :
    Nat.card (W.torsion (3 ^ k)) = 9 ^ k := by
  rw [card_torsion_pow_of_surjective (nsmul_three_surjective h2) k, card_torsion_three h2 h3]

/-- `E[3^k]` is finite. This is read off the count `#E[3^k] = 9^k ≠ 0` rather than from the
`3`-smooth finiteness of `EllipticCurves.Torsion.Multiplicative`, matching how
`finite_torsion_two_pow` is obtained; here neither hypothesis is spurious, since both are already
carried by the count. -/
theorem finite_torsion_three_pow (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (k : ℕ) :
    Finite (W.torsion (3 ^ k)) :=
  finite_torsion_pow three_ne_zero (nsmul_three_surjective h2)
    (by rw [card_torsion_three h2 h3]; norm_num) k

/-- **`#E[3^k] = 3^k · 3^k`**, the same count as `card_torsion_three_pow` in the shape every
consumer that compares `E[3^k]` with `(ZMod (3^k))²` needs it: as a product of two copies of the
modulus rather than as a power of `9`.

⚠️ `9 ^ k` is **not** definitionally `3 ^ k * 3 ^ k`, so the conversion is a real rewrite and not a
`rfl`. It is stated at general `p` in `EllipticCurves.Torsion.PrimaryTower` rather than repeated at
each call site; `EllipticCurves.Torsion.TwoPrimary.card_torsion_two_pow_mul_self` is the other
instance. -/
theorem card_torsion_three_pow_mul_self (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (k : ℕ) :
    Nat.card (W.torsion (3 ^ k)) = 3 ^ k * 3 ^ k :=
  card_torsion_pow_mul_self (nsmul_three_surjective h2)
    (by rw [card_torsion_three h2 h3]; norm_num) k

/-! ## The structure of `E[3^k]` -/

/-- **The structure theorem for `E[3^k]`**: over an algebraically closed field in which `2 ≠ 0` and
`3 ≠ 0`, the `3^k`-torsion subgroup of an elliptic curve is isomorphic to `ℤ/3^kℤ × ℤ/3^kℤ`.

The count `#E[3^k] = 9^k = (3^k)²` goes into the classification core
`AddCommGroup.equiv_zmod_sq_of_card_sq`, whose rank hypothesis is checked prime by prime — and that
check is now run once, at general `p`, in `nonempty_torsionPow_addEquiv`.

⚠️ **This docstring used to call its case split "the mirror image" of the one in
`nonempty_torsionTwoPow_addEquiv` and "not symmetric", and that was the shape of the abstraction
seen from the inside.** At general prime `p` the split is `q = p` (the counting branch, using
`#E[p] = p²`) against every `q ≠ p` (the coprimality branch, where an element killed by both `q` and
`p ^ k` is killed by `1`). ⚠️ `Nat.prime_three` is the **only** thing this instance adds to the two
inputs, and primality is needed for nothing else in the tower. -/
theorem nonempty_torsionThreePow_addEquiv (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (k : ℕ) :
    Nonempty (W.torsion (3 ^ k) ≃+ ZMod (3 ^ k) × ZMod (3 ^ k)) :=
  nonempty_torsionPow_addEquiv Nat.prime_three (nsmul_three_surjective h2)
    (by rw [card_torsion_three h2 h3]; norm_num) k

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

/-- **`#E[n] = n²` with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, for every `3`-smooth `n ≠ 0`.** The
hypotheses are exactly those of `EllipticCurves.Torsion.Multiplicative`'s
`card_torsion_le_sq_of_smooth`, with `≤` upgraded to `=`: the `3`-smooth bound is sharp. -/
theorem card_torsion_eq_sq_of_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) : Nat.card (W.torsion n) = n ^ 2 := by
  obtain ⟨a, b, rfl⟩ := Nat.exists_eq_two_pow_mul_three_pow n hn hfac
  exact card_torsion_two_pow_mul_three_pow h2 h3 a b

/-- **`E[n] ≃+ ℤ/nℤ × ℤ/nℤ` with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, for every `3`-smooth `n ≠ 0`**:
the widest slice of the structure theorem `E[n] ≅ (ℤ/nℤ)²` available in this development, and the
first index it does not cover is `n = 5`. -/
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

/-! The certificate curve `y² + y = x³` over `ℚ` — this development's standard `n = 3` curve,
chosen because `Ψ₃ = 3X(X³ + 1)` factors and `(0, 0)` is a rational `3`-torsion point — and its
algebraically closed base are the shared `EllipticCurves.Fixture.y2AddYEqX3` and
`EllipticCurves.Fixture.AlgClosedQ`, which also supply `(y2AddYEqX3 ℚ).IsElliptic` from a single
`[CharZero F]` instance. The **base-changed** `((y2AddYEqX3 ℚ)⁄AlgClosedQ).IsElliptic` comes from
the same module, via `EllipticCurves.Fixture.instIsEllipticBaseChange`; this block declares no
fixture of its own (`#1408`). -/

open EllipticCurves.Fixture

/-- Every prime factor of `72 = 2³ · 3²` is `2` or `3`. -/
private lemma primeFactors_seventytwo : ∀ p ∈ (72 : ℕ).primeFactors, p = 2 ∨ p = 3 := by
  intro p hp
  obtain ⟨hpp, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
  rw [show (72 : ℕ) = 2 ^ 3 * 3 ^ 2 from rfl] at hdvd
  rcases (Nat.Prime.dvd_mul hpp).mp hdvd with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp (hpp.dvd_of_dvd_pow h))

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

open Classical in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on a curve that exists, `E[9]` really has `81` points, so
the `3`-primary tower is not a statement about an empty family of curves. -/
example : Nat.card (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 9) = 81 :=
  card_torsion_nine exampleTwo exampleThree

open Classical in
/-- The structure statement at the same index, restated in full rather than projected out of an
existential. -/
example : Nonempty (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 9 ≃+ ZMod 9 × ZMod 9) :=
  nonempty_torsionNine_addEquiv exampleTwo exampleThree

open Classical in
/-- The `3`-smooth headline at an index no earlier file could reach: `72 = 2³ · 3²` is neither a
prime power nor of the form `2 ^ k · 3`.

⚠️ The `3`-smoothness side condition is **not** `by decide`: the `Decidable` instance for
`∀ p ∈ Nat.primeFactors 72, p = 2 ∨ p = 3` gets stuck rather than reducing, with
`reduction got stuck at the Decidable instance List.decidableBAll …`. It is discharged by
`primeFactors_seventytwo` above instead, which is the specialisation of
`EllipticCurves.Torsion.Multiplicative`'s private `primeFactors_two_pow_mul_three_pow`. -/
example : Nat.card (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 72) = 5184 := by
  have h := card_torsion_eq_sq_of_smooth (W := (y2AddYEqX3 ℚ)⁄AlgClosedQ) exampleTwo
    exampleThree (n := 72) (by norm_num) primeFactors_seventytwo
  norm_num at h
  exact h

end Nonvacuity

end WeierstrassCurve.Affine
