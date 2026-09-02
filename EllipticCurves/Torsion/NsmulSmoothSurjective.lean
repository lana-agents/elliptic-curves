/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.Torsion.ThreePrimary

/-!
# `[n]` is surjective on `E(F̄)` at every `3`-smooth `n`

`EllipticCurves.Torsion.DoublingSurjective` proves `nsmul_two_surjective` and
`EllipticCurves.Torsion.TriplingSurjective` proves `nsmul_three_surjective`: over an algebraically
closed field in which `2` is invertible, every point is twice — and three times — another point.
Each is a genuine computation, run through `nsmul_surjective_of_hasXCoordFormula` on the explicit
coordinate formula at that index.

⚠️ **Both take `(2 : F) ≠ 0` and neither takes `(3 : F) ≠ 0`**, the tripling half included: it is
derived through `hasXCoordFormula_three h2` (`EllipticCurves.Torsion.TriplingSurjective`), whose
only field hypothesis is `h2`.  That is why `exists_two_pow_mul_three_pow_nsmul_eq` below carries
`h2` and nothing else, and it is the one place in this file where a reader is likely to expect a
hypothesis that is not there.

**Surjectivity is multiplicative in the index and nothing in this tree said so.**  `[m · n] = [m] ∘
[n]` on points is `mul_smul`, so the composite of two surjections is one, and the two merged indices
generate every `3`-smooth `n`.  That is this file: `exists_nsmul_eq_of_smooth` and
`nsmul_surjective_of_smooth`, at every `n ≠ 0` all of whose prime factors are `2` or `3`.

## ⚠️ Why this is not a coordinate formula in disguise, and where the ceiling is

The `n = 2` and `n = 3` proofs both go through `hasXCoordFormula`, which says that
`x(n • P) = Φₙ/ΨSqₙ` at that index — the merged low-index slices of `#251`.  **Nothing in this file
adds a new index to that list.**  What it adds is the observation that the *conclusion* composes
even though the *route to it* does not, so the general-`n` coordinate formula is not on the critical
path for surjectivity at a `3`-smooth index.

⚠️ **This paragraph used to end *"`n = 5` is unmoved … a fifth index would need `hasXCoordFormula`
at `5`, which is `#251` at general `n` and is Ward-gated (`#260`)"*, and that ceiling is gone.**
`hasXCoordFormula_of_two_ne_zero` (`EllipticCurves.Torsion.NsmulOrder`) holds at **every** index
over any field with `(2 : F) ≠ 0`, and `nsmul_surjective_of_two_ne_zero`
(`EllipticCurves.Torsion.TwoTorsionOrder`) is this file's headline **with the `3`-smoothness
dropped**: same `[IsAlgClosed F]`, same `[W.IsElliptic]`, same `(2 : F) ≠ 0`, every `n ≠ 0`.  So
`nsmul_surjective_of_smooth` is a strict specialisation of a merged theorem, and `n = 5` *is*
moved — elsewhere.

⚠️ **That is not a reason to delete this file, and the reason is import position, not novelty.**
`Torsion.NsmulSmoothSurjective` and `Torsion.TwoTorsionOrder` are **import-incomparable** — closures
of **19** and **24** `EllipticCurves` modules, neither containing the other — so routing this file's
consumers (`FunctionField.MulByNFibre`, `FunctionField.WeilPairingAlternatingAssemblyN`) through the
general theorem would move them onto a different stack, not remove one.  The same pattern is
already in the tree: `card_torsion_le_sq_of_smooth` (`EllipticCurves.Torsion.Multiplicative`,
closure **7**) sits beside the general `card_torsion_le_sq` (`EllipticCurves.Torsion.XSupport`,
closure **23**).  What is genuinely this file's is unchanged: the *conclusion* composes along
`mul_smul` even where the route to it does not.

⚠️ **The two statements this paragraph used to call "the same ceiling" no longer agree with each
other.**  `card_torsion_eq_sq_of_smooth` (`EllipticCurves.Torsion.ThreePrimary`) is still
`3`-smooth.  ⚠️ The reason this sentence used to give — *"because `#E[n] = n²` is"* — is false:
`card_torsion_eq_sq_of_odd` (`EllipticCurves.Torsion.OmegaChordSum`) proves `#E[n] = n²` at every
odd `n`, so what is `3`-smooth is that one lemma's range, not the count.
`transcendental_xCoord_nsmul_of_smooth`
(`EllipticCurves.FunctionField.MulByNComposition`) is not a ceiling any more: at a `3`-smooth `n`
its own `(2 : F) ≠ 0` and `(3 : F) ≠ 0` give `(n : F) ≠ 0`, which is all
`transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`
(`EllipticCurves.FunctionField.MulByNXCoordFormula`) asks.  ⚠️ That substitution is *not* made
anywhere and the import direction for it was not measured; what is claimed here is only that the
`3`-smoothness of this file is no longer a coordinate-formula ceiling, so a reader hunting the
surviving obstruction should not stop here.

## Main statements

⚠️ Every public declaration of this file is listed.

* `WeierstrassCurve.Affine.exists_two_pow_mul_three_pow_nsmul_eq` — the double induction, at an
  index presented as `2 ^ a * 3 ^ b`;
* **`WeierstrassCurve.Affine.exists_nsmul_eq_of_smooth`** — the headline, `∃ P, n • P = Q` at every
  `3`-smooth `n ≠ 0`;
* `WeierstrassCurve.Affine.nsmul_surjective_of_smooth` — the same as a `Function.Surjective`, the
  form `EllipticCurves.Torsion.Divisible`'s `torsionSmulHom_surjective` and
  `EllipticCurves.Torsion.PrimaryTower`'s `card_torsion_pow_of_surjective` consume.

## What is *not* here

* **No new index.**  The two merged surjectivity theorems are the only inputs; nothing is proved at
  a prime other than `2` and `3`.  In particular this is not progress on `#251` — ⚠️ **whose
  coordinate formula has since been closed at every index** (`hasXCoordFormula_of_two_ne_zero`,
  `EllipticCurves.Torsion.NsmulOrder`), so the sentence that used to end *"which is the live gate"*
  is retired: nothing here stands between the tree and a fifth index.  ⚠️ This bullet used to name
  `#404` beside it; `#404`'s on-curve identity is closed
  (`EllipticCurves.Torsion.OmegaCrux`, PR #557) and was never what `HasXCoordFormula` needed.
* **No injectivity, no degree, and no statement about `E[n]`.**  `#E[n] = n²` at `3`-smooth `n` is
  `card_torsion_eq_sq_of_smooth`, already merged, and it is an *input* to the consumers of this
  file rather than an output of it.
* **Nothing over a field that is not algebraically closed.**  `[IsAlgClosed F]` is inherited from
  both inputs and is not removable: over `ℚ` the curve `y² = x³ − x` has `[2]` non-surjective on
  rational points.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.10 — `[n]` is
  surjective on `E(K̄)` for every `n ≠ 0`.  ⚠️ That statement is *wider* than this file, which is
  `3`-smooth `n` only.  ⚠️ This bullet used to add *"reaching it here needs the coordinate formula
  this file does not have"*, and that reads as a claim the formula is unavailable, which it is not:
  the general-`n` form is on `main` as `nsmul_surjective_of_two_ne_zero`
  (`EllipticCurves.Torsion.TwoTorsionOrder`), off `hasXCoordFormula_of_two_ne_zero`
  (`EllipticCurves.Torsion.NsmulOrder`).  What stays true is the **import** claim: neither module is
  in this file's closure, so the elementary `3`-smooth argument below is genuinely independent
  of them.
-/

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} [IsAlgClosed F] [W.IsElliptic]

/-- **`[2 ^ a · 3 ^ b]` is surjective on `E(F̄)`.**

Induction on `a` and then on `b`, peeling one prime off the index at each step: a preimage under
`[2]` (or `[3]`) of `Q`, then a preimage of *that* under the smaller index.  ⚠️ The `mul_smul`
rewrite is where the composition happens, and it is the whole argument — neither merged input is
re-proved and no coordinate formula is evaluated at a new index. -/
theorem exists_two_pow_mul_three_pow_nsmul_eq (h2 : (2 : F) ≠ 0) (a b : ℕ) (Q : W.Point) :
    ∃ P : W.Point, (2 ^ a * 3 ^ b) • P = Q := by
  induction a generalizing Q with
  | zero =>
    induction b generalizing Q with
    | zero => exact ⟨Q, by simp⟩
    | succ b ih =>
      obtain ⟨P₁, hP₁⟩ := exists_nsmul_three_eq h2 Q
      obtain ⟨P, hP⟩ := ih P₁
      exact ⟨P, by rw [show 2 ^ 0 * 3 ^ (b + 1) = 3 * (2 ^ 0 * 3 ^ b) by ring, mul_smul, hP, hP₁]⟩
  | succ a ih =>
    obtain ⟨P₁, hP₁⟩ := exists_nsmul_two_eq h2 Q
    obtain ⟨P, hP⟩ := ih P₁
    exact ⟨P, by rw [show 2 ^ (a + 1) * 3 ^ b = 2 * (2 ^ a * 3 ^ b) by ring, mul_smul, hP, hP₁]⟩

/-- **`[n]` is surjective on `E(F̄)` at every `3`-smooth `n ≠ 0`**: every point is `n` times another
one.

The hypotheses are exactly those of `card_torsion_eq_sq_of_smooth`
(`EllipticCurves.Torsion.ThreePrimary`), and `n = 5` is the first index not covered. -/
theorem exists_nsmul_eq_of_smooth (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) (Q : W.Point) : ∃ P : W.Point, n • P = Q := by
  obtain ⟨a, b, rfl⟩ := Nat.exists_eq_two_pow_mul_three_pow n hn hfac
  exact exists_two_pow_mul_three_pow_nsmul_eq h2 a b Q

/-- **`[n]` is surjective on `E(F̄)` at every `3`-smooth `n ≠ 0`**, stated as
`Function.Surjective` — the `3`-smooth analogue of `nsmul_two_surjective` and
`nsmul_three_surjective`. -/
theorem nsmul_surjective_of_smooth (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) :
    Function.Surjective fun P : W.Point => n • P :=
  exists_nsmul_eq_of_smooth h2 hn hfac

/-! ### Non-vacuity

⚠️ `[IsAlgClosed F]` plus `[W.IsElliptic]` plus `3`-smoothness is three hypotheses at once, and a
theorem whose hypotheses could not be met would be vacuous.  A curve on which all three elaborate is
committed rather than quoted. -/

section Nonvacuity

/-! The base and the curve are the shared `EllipticCurves.Fixture.AlgClosedQ` — an algebraic
closure of `ℚ`, so `[IsAlgClosed F]` and `(2 : F) ≠ 0` are both available — and
`EllipticCurves.Fixture.y2AddYEqX3` at that base: `y² + y = x³`, of discriminant `−27`.  ⚠️ The
curve is stated over the closure rather than over `ℚ` because `nsmul_surjective_of_smooth` asks for
`[IsAlgClosed F]`; that is the difference between this block and the `ℚ`-based ones in
`Torsion.DoublingSurjective` and `Torsion.TriplingSurjective`, whose whole point is that no closure
is needed.  `(y2AddYEqX3 AlgClosedQ).IsElliptic` comes from the single `[CharZero F]` instance in
`Fixtures`; the `DecidableEq` instance below is not a fixture and stays here. -/

open EllipticCurves.Fixture

private noncomputable instance : DecidableEq AlgClosedQ := Classical.decEq _

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

/-- ⚠️ `decide` does **not** close this: `Nat.primeFactors` goes through `Nat.primeFactorsList`,
whose `Decidable` instance gets stuck on `Nat.minFac`'s well-founded recursion.  Bounding `p` and
case-splitting is what works. -/
private lemma smoothTwelve : ∀ p ∈ Nat.primeFactors 12, p = 2 ∨ p = 3 := by
  intro p hp
  obtain ⟨hp1, hp2, -⟩ := Nat.mem_primeFactors.mp hp
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) hp2
  interval_cases p <;> revert hp1 hp2 <;> decide

/-- **`[12]` is surjective on `y² + y = x³` over `AlgebraicClosure ℚ`, committed** — an index at
which neither merged surjectivity theorem says anything. -/
example : Function.Surjective fun P : (y2AddYEqX3 AlgClosedQ).Point => (12 : ℕ) • P :=
  nsmul_surjective_of_smooth (W := y2AddYEqX3 AlgClosedQ) exampleTwo (by norm_num) smoothTwelve

end Nonvacuity

end WeierstrassCurve.Affine
