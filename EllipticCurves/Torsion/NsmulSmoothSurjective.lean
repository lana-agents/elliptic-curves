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
closed field — ⚠️ **in every characteristic, since `#2253`; this sentence read *"in which `2` is
invertible"*** — every point is twice — and three times — another point.
Each is a genuine computation, run through `nsmul_surjective_of_hasXCoordFormula` on the explicit
coordinate formula at that index.

⚠️ **NEITHER TAKES ANY FIELD HYPOTHESIS AT ALL, as of `#2253`** — this paragraph read *"Both take
`(2 : F) ≠ 0` and neither takes `(3 : F) ≠ 0`"*, and the chain below it is the record of where that
`h2` went.  It was never in the coordinate formula: `hasXCoordFormula_three`
(`EllipticCurves.Torsion.TriplingSurjective`) carries **no** field hypothesis — vacuous at `#2242`,
binder removed at `#2245` — and `hasXCoordFormula_two` never had one.  What bound `h2` was
`exists_nsmul_some_of_hasXCoordFormula` / `exists_nsmul_eq_of_hasXCoordFormula`
(`EllipticCurves.Torsion.NsmulSurjective`), which spent it on `exists_equation`: finding a point
above a given `x` means solving a quadratic in `y`.  ⚠️ **And over an algebraically closed field
that quadratic never needed `2` invertible** — `exists_equation'`
(`EllipticCurves.Torsion.ThreeTorsionStructure`, `#2251`) solves it by `IsAlgClosed.exists_root` in
every characteristic — so `#2253` removed the binder from that pair and from
`exists_two_pow_mul_three_pow_nsmul_eq` and `exists_nsmul_eq_of_smooth` below.  **This file now
binds no field hypothesis anywhere, and that is the one place in it where a reader is likely to
expect one that is not there.**

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
dropped**: same `[IsAlgClosed F]`, same `[W.IsElliptic]`, every `n ≠ 0`.  ⚠️ **The two are NO LONGER
ordered by inclusion of hypotheses, and that is `#2253`'s doing**: this clause read *"same
`(2 : F) ≠ 0`"*, and the general form still carries it — through `hasXCoordFormula_of_two_ne_zero`,
which is `#2250` and open — while this file's headline no longer does.  So at a `3`-smooth index the
smooth route is strictly the weaker-hypothesis one, and `n = 5` *is* moved — elsewhere, at the price
of an `h2`.

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
(`EllipticCurves.FunctionField.MulByNXCoordFormula`) asks.  ⚠️ **RETIRED — the substitution has
been made and its import cost measured.**  This clause read *"That substitution is not made anywhere
and the import direction for it was not measured"* (`6af226f`, `#1499`, PR #575, 2026-09-02).  It
was made the next day, at `d780bf8` (`#1549` group 2, PR #608, 2026-09-03), in
`EllipticCurves.FunctionField.WeilPairingTranslationSlotHprinN`, whose `…_of_ne_zero_of_hprin`
statements are its consequence and whose docstring records the cost as **one `import`**;
`EllipticCurves.FunctionField.WeilPairingGaloisRootN` carries the same pair.  ⚠️ What is claimed
here is unchanged: the `3`-smoothness of this file is no longer a coordinate-formula ceiling, so a
reader hunting the surviving obstruction should not stop here.

## Main statements

⚠️ Every public declaration of this file is listed.

* `WeierstrassCurve.Affine.exists_two_pow_mul_three_pow_nsmul_eq` — the double induction, at an
  index presented as `2 ^ a * 3 ^ b`;
* **`WeierstrassCurve.Affine.exists_nsmul_eq_of_smooth`** — the headline, `∃ P, n • P = Q` with no
  field hypothesis, at every `3`-smooth `n ≠ 0`;
* `WeierstrassCurve.Affine.nsmul_surjective_of_smooth` — the same as a `Function.Surjective`, the
  form `EllipticCurves.Torsion.Divisible`'s `torsionSmulHom_surjective` and
  `EllipticCurves.Torsion.PrimaryTower`'s `card_torsion_pow_of_surjective` consume.

## What is *not* here

* **No new index.**  The two merged surjectivity theorems are the only inputs; nothing is proved at
  a prime other than `2` and `3`.  In particular this is not progress on `#251` — ⚠️ **whose
  coordinate formula has since been closed at every index with `(2 : F) ≠ 0`**
  (`hasXCoordFormula_of_two_ne_zero`, `EllipticCurves.Torsion.NsmulOrder`), so the sentence that
  used to end *"which is the live gate"* is retired: nothing here stands between the tree and a
  fifth index.  ⚠️ This bullet used to name `#404` beside it; `#404`'s on-curve identity is closed
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
theorem exists_two_pow_mul_three_pow_nsmul_eq (a b : ℕ) (Q : W.Point) :
    ∃ P : W.Point, (2 ^ a * 3 ^ b) • P = Q := by
  induction a generalizing Q with
  | zero =>
    induction b generalizing Q with
    | zero => exact ⟨Q, by simp⟩
    | succ b ih =>
      obtain ⟨P₁, hP₁⟩ := exists_nsmul_three_eq Q
      obtain ⟨P, hP⟩ := ih P₁
      exact ⟨P, by rw [show 2 ^ 0 * 3 ^ (b + 1) = 3 * (2 ^ 0 * 3 ^ b) by ring, mul_smul, hP, hP₁]⟩
  | succ a ih =>
    obtain ⟨P₁, hP₁⟩ := exists_nsmul_two_eq Q
    obtain ⟨P, hP⟩ := ih P₁
    exact ⟨P, by rw [show 2 ^ (a + 1) * 3 ^ b = 2 * (2 ^ a * 3 ^ b) by ring, mul_smul, hP, hP₁]⟩

/-- **`[n]` is surjective on `E(F̄)` at every `3`-smooth `n ≠ 0`**: every point is `n` times another
one.  ⚠️ **In every characteristic**, since `#2253`.

⚠️ The hypotheses are those of `card_torsion_eq_sq_of_smooth`
(`EllipticCurves.Torsion.ThreePrimary`) **minus both `(3 : F) ≠ 0` and `(2 : F) ≠ 0`**, neither of
which this statement takes: on both axes it is strictly the more general of the two, and the
asymmetry is the point — `[n]` is surjective on `E(F̄)` in every characteristic while
`#E[2^a·3^b] = (2^a·3^b)²` is false in characteristic `2` and in characteristic `3`.  `n = 5` is the
first index not covered. -/
theorem exists_nsmul_eq_of_smooth {n : ℕ} (hn : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) (Q : W.Point) : ∃ P : W.Point, n • P = Q := by
  obtain ⟨a, b, rfl⟩ := Nat.exists_eq_two_pow_mul_three_pow n hn hfac
  exact exists_two_pow_mul_three_pow_nsmul_eq a b Q

/-- **`[n]` is surjective on `E(F̄)` at every `3`-smooth `n ≠ 0`**, in every characteristic, stated
as `Function.Surjective` — the `3`-smooth analogue of `nsmul_two_surjective` and
`nsmul_three_surjective`. -/
theorem nsmul_surjective_of_smooth {n : ℕ} (hn : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) :
    Function.Surjective fun P : W.Point => n • P :=
  exists_nsmul_eq_of_smooth hn hfac

/-! ### Non-vacuity

⚠️ `[IsAlgClosed F]` plus `[W.IsElliptic]` plus `3`-smoothness is three hypotheses at once, and a
theorem whose hypotheses could not be met would be vacuous.  A curve on which all three elaborate is
committed rather than quoted.  ⚠️ **Two curves, since `#2253`**: one in characteristic zero, which
is the block that was here, and one in characteristic `2`, which is the block the removed hypothesis
makes possible and which is the only evidence that removing it bought anything. -/

section Nonvacuity

/-! The base and the curve are the shared `EllipticCurves.Fixture.AlgClosedQ` — an algebraic
closure of `ℚ`, so `[IsAlgClosed F]` is available — and `EllipticCurves.Fixture.y2AddYEqX3` at that
base: `y² + y = x³`, of discriminant `−27`.  ⚠️ The curve is stated over the closure rather than
over `ℚ` because `nsmul_surjective_of_smooth` asks for `[IsAlgClosed F]`; that is the difference
between
this block and the `ℚ`-based ones in `Torsion.DoublingSurjective` and `Torsion.TriplingSurjective`,
whose whole point is that no closure is needed.  `(y2AddYEqX3 AlgClosedQ).IsElliptic` comes from the
single `[CharZero F]` instance in `Fixtures`; the `DecidableEq` instance below is not a fixture and
stays here.

⚠️ **This block used to also carry `private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0`, and `#2253`
deleted it rather than leaving it unreferenced**: it existed only to feed the `h2` argument of
`nsmul_surjective_of_smooth`, which no longer has one.  A dead `private` helper is not flagged by
any linter, which is exactly why it is named here. -/

open EllipticCurves.Fixture

private noncomputable instance : DecidableEq AlgClosedQ := Classical.decEq _

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
  nsmul_surjective_of_smooth (W := y2AddYEqX3 AlgClosedQ) (by norm_num) smoothTwelve

/-! ### ⚠️ Non-vacuity in characteristic `2`, which is the whole content of `#2253`

⚠️ **The block above lives over an algebraic closure of `ℚ`, where `(2 : F) ≠ 0` holds — so it
certifies that the hypotheses can be met and says nothing at all about the hypothesis `#2253`
removed.**  A round that drops a hypothesis owes a witness that the hypothesis was excluding
something real.  This is that witness: `y² + xy = x³ + 1` over `AlgebraicClosure (ZMod 2)`, the
tuple `⟨1, 0, 0, 0, 1⟩`, on the **ordinary** branch `a₁ ≠ 0`.  ⚠️ **It is the same tuple
`EllipticCurves.Torsion.ThreeTorsionStructure` uses to certify `exists_equation'` itself**, and the
same one `EllipticCurves.Torsion.TriplingSurjective` and `EllipticCurves.Torsion.TwoTorsionCharTwo`
use over `ZMod 2`.

⚠️ **The three helpers are restated here rather than imported because that file's are `private`** —
checked, not assumed, and `private` is not `protected`.  Four lines of re-proof is a smaller price
than widening another file's interface for a witness.

⚠️ **`[2]` and `[3]` really are surjective on `E(F̄)` in characteristic `2`, and the two `example`s
below are what say so.**  What is *not* true there, and is not claimed anywhere by this file, is
`#E[2] = 4`: in characteristic `2` the `2`-torsion has at most two points
(`EllipticCurves.Torsion.TwoTorsionCharTwo`), so `card_torsion_two` and every counting theorem
downstream of it keeps its `(2 : F) ≠ 0` and is right to.  ⚠️ **Surjectivity of `[n]` and the order
of `E[n]` come apart exactly here, and that is the boundary `#2253` draws.**

⚠️ **No `decide` is available over this field**, which carries no `DecidableEq` — the `Δ = 1`
arithmetic goes through `linear_combination` against `two_eq_zero_closureCharTwo` instead, and the
`DecidableEq` the `Point` group structure needs is `Classical.decEq`, as over `AlgClosedQ` above. -/

/-- The base field really is of characteristic `2`, which is what makes the `example`s below
statements that the `(2 : F) ≠ 0` forms could not even express. -/
private lemma two_eq_zero_closureCharTwo : (2 : AlgebraicClosure (ZMod 2)) = 0 := by
  have : CharP (AlgebraicClosure (ZMod 2)) 2 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2))).injective 2
  exact_mod_cast CharP.cast_eq_zero (AlgebraicClosure (ZMod 2)) 2

private noncomputable instance : DecidableEq (AlgebraicClosure (ZMod 2)) := Classical.decEq _

/-- `y² + xy = x³ + 1` over `AlgebraicClosure (ZMod 2)` — the tuple `⟨1, 0, 0, 0, 1⟩`.

⚠️ `noncomputable` because `AlgebraicClosure.instField` is, not because anything here is. -/
private noncomputable def curveClosureCharTwo : Affine (AlgebraicClosure (ZMod 2)) :=
  ⟨1, 0, 0, 0, 1⟩

/-- `Δ = 1`, so the witness is not a singular equation dressed up as one: `b₂ = 1`, `b₄ = 0`,
`b₆ = 4`, `b₈ = 1` and `Δ = -b₂²b₈ - 8b₄³ - 27b₆² + 9b₂b₄b₆ = -433 = 1 - 217 · 2`. -/
private lemma Δ_curveClosureCharTwo : curveClosureCharTwo.Δ = 1 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, curveClosureCharTwo]
  linear_combination (-217 : AlgebraicClosure (ZMod 2)) * two_eq_zero_closureCharTwo

private instance : curveClosureCharTwo.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, Δ_curveClosureCharTwo]
  exact isUnit_one

/-- **`[2]` is surjective on `y² + xy = x³ + 1` over `AlgebraicClosure (ZMod 2)`, committed.**
⚠️ This is a statement the `(2 : F) ≠ 0` form of `nsmul_two_surjective` cannot be instantiated at,
because `two_eq_zero_closureCharTwo` proves its hypothesis false over this field. -/
example : Function.Surjective fun P : curveClosureCharTwo.Point => (2 : ℕ) • P :=
  nsmul_two_surjective

/-- **`[3]` is surjective on the same curve, in characteristic `2`, committed** — so the `h2` that
`#690` already showed was not an `h3` in disguise was not a hypothesis on the characteristic at
all. -/
example : Function.Surjective fun P : curveClosureCharTwo.Point => (3 : ℕ) • P :=
  nsmul_three_surjective

/-- **`[12]` is surjective on the same curve, in characteristic `2`, committed** — this file's own
headline at an index neither merged theorem reaches, over a field neither could be stated over. -/
example : Function.Surjective fun P : curveClosureCharTwo.Point => (12 : ℕ) • P :=
  nsmul_surjective_of_smooth (W := curveClosureCharTwo) (by norm_num) smoothTwelve

end Nonvacuity

end WeierstrassCurve.Affine
