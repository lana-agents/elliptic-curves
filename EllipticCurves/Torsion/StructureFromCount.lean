/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.AbelianStructure
import EllipticCurves.Torsion.EvenTorsionCountSplits
import EllipticCurves.Torsion.StructureGeneral

/-!
# The structure theorem from the COUNT alone, with no algebraically closed field

`E[n] ≃+ ZMod n × ZMod n` at **every** `n`, over **any** field with `(2 : F) ≠ 0` and
`(n : F) ≠ 0`, **given only the count `#E[n] = n²`**.

`EllipticCurves.Torsion.StructureGeneral`'s `nonempty_torsion_addEquiv` proves the same conclusion
under the same two characteristic conditions and additionally `[IsAlgClosed F]`.  ⚠️⚠️ **This file's
`nonempty_torsion_addEquiv_of_card` subsumes it — the `example` in `### Recoveries` below is that
claim, machine-checked — and the point is the DIAGNOSIS: the closure there is an artefact of the
ROUTE and not of the statement.**

## ⚠️⚠️ Where the closure was being spent, measured declaration by declaration

`nonempty_torsion_addEquiv` reduces by `Nat.recOnPosPrimePosCoprime` to a prime-power case and a
coprime case.  Walking its inputs and asking of each whether it binds `[IsAlgClosed F]`, whether
that binder is **necessary for the statement as written**, and whether the declaration is needed on
the route below:

| input | binds it | necessary **as written** | needed below |
|---|---|---|---|
| `nonempty_torsion_addEquiv` (`StructureGeneral`) | yes, `variable` | **YES** | — |
| `nonempty_torsionPrimePow_addEquiv` (`StructureGeneral`) | yes, `variable` | **YES** | **no** |
| `nonempty_torsionPow_addEquiv` (`PrimaryTower`) | **no** | — | **no** |
| `nsmul_surjective_of_two_ne_zero` (`TwoTorsionOrder`) | **yes, own** | **YES** | **no** |
| `card_torsion_eq_sq` (`StructureGeneral`) | yes, `variable` | **YES** | no |
| `nonempty_torsionTwoPow_addEquiv` (`TwoPrimary`) | yes, `variable` | **YES** | **no** |
| `nonempty_torsion_addEquiv_zmod_sq_of_coprime` (`CoprimeStructure`) | **no** | — | **no** |
| `AddCommGroup.equiv_zmod_sq_of_card_sq` (`AbelianStructure`) | **no** | — | **yes** |
| `card_torsion_le_sq` (`XSupport`) | **no** | — | **yes** |

⚠️⚠️ **The "necessary" column is `YES` at every gated row, and reading it as `no` anywhere would be
a FALSE claim about those theorems.**  Each of them asserts its conclusion with **no replacement
hypothesis**, and each conclusion is false over `ℚ`: `#E[n] = n²` fails there, `E[n] ≅ (ℤ/nℤ)²`
fails there, and `[n]` is not surjective on `E(ℚ)`.  ⚠️ **So nothing below widens any of those five
statements, and this file is not a widening of anything.**  What it changes is the **route**: the
count becomes a **hypothesis**, and with the count supplied the closure is not needed.

⚠️ **The five gated occurrences separate into three kinds, and the distinction is the whole
content of this section:**

1. **Tradeable.**  `card_torsion_eq_sq`'s closure can be exchanged for splitting hypotheses, and
   `#2307` did exactly that: `EllipticCurves.Torsion.EvenTorsionCountSplits`'
   `card_torsion_eq_sq_of_splits_of_splits_Ψ₂Sq` is the same conclusion from three conditions over
   the base field.  ⚠️ **That is a different statement and not a widened one.**
2. **Not tradeable by anything in the tree.**  `nsmul_surjective_of_two_ne_zero` — surjectivity of
   `[n]` on `E(F)` — is **false** over a field that is not algebraically closed, and **no splitting
   hypothesis repairs it**: `E(ℚ)` at `n = 2` is the standard counterexample.  `#2328`'s
   *"if a necessary `[IsAlgClosed F]` is found, say so and STOP"* applies to this declaration.
3. **Avoidable by route.**  Everything that exists only to get from `#E[p] = p²` to the structure —
   `nonempty_torsionPrimePow_addEquiv`, `nonempty_torsionTwoPow_addEquiv` and the primary tower
   behind them.  ⚠️⚠️ **This is where the finding is: a caller who already has the count at `n` has
   nothing to induct over, and the surjectivity those steps pay for is bought to supply a count.**

⚠️ **`[IsAlgClosed F]` reaches four of the nine through a `variable` line that none of them names in
its own binder list**, which is why the gap is invisible at any one theorem's source:
`StructureGeneral`:`156`, `TwoPrimary`:`132`, `CoprimeStructure`:`107` and `PrimaryTowerOdd`:`154`
each carry one, and the first two are the ones on this route.  ⚠️⚠️ **`CoprimeStructure`'s is at
`:107` and the theorem that matters sits at `:94`, ABOVE it — so that theorem is closure-free, and
line order is what decides it; `#check @` is what proves it and is what this round ran.** ⚠️
**`PrimaryTower` carries the string twice and in neither case as a binder** — both occurrences are
its own module docstring saying *"No hypothesis on the field … consumed entirely by the two
inputs"*, which is **true** and is the clue this file followed.  ⚠️ **So `git grep -c IsAlgClosed`
is NOT the test; ask of each occurrence whether it is a binder.**

## The route, and why it is shorter rather than cleverer

`AddCommGroup.equiv_zmod_sq_of_card_sq` (`EllipticCurves.Torsion.AbelianStructure`) is already a
**general-`n`** classification core, not a prime-power one: a finite abelian group killed by `n > 0`
with `Nat.card A = n ^ 2` and `#A[q] ≤ q ^ 2` at every prime `q` is `ZMod n × ZMod n`.  ⚠️ **So the
primary tower is not needed at all** — it exists to produce `#E[pᵏ] = (pᵏ)²` from `#E[p] = p²`, and
a caller who already has the count at `n` has nothing to induct over.

The three hypotheses of the core are discharged as follows.

* `∀ a : W.torsion n, n • a = 0` is `nsmul_mem_torsion`, a definitional unfolding.
* `Nat.card (W.torsion n) = n ^ 2` is the hypothesis of this file's theorem.
* The rank bound `#E[n][q] ≤ q ^ 2` at a prime `q` splits on `q ∣ n`:
  * **`q ∣ n`.** `E[n][q]` injects into `E[q]` — the injection is the identity on points, and the
    membership side condition is `congrArg Subtype.val` — and `#E[q] ≤ q ^ 2` is
    `EllipticCurves.Torsion.XSupport`'s `card_torsion_le_sq`, which binds `(2 : F) ≠ 0` and
    `(q : F) ≠ 0` and ⚠️ **no closure: `git grep -c IsAlgClosed` over that file returns `0`.**
    `(q : F) ≠ 0` comes from `q ∣ n` and `(n : F) ≠ 0`.
  * **`q ∤ n`.** An element of `E[n]` killed by `q` is killed by `1`, by Bézout on
    `IsCoprime (q : ℤ) (n : ℤ)`, so the set is a singleton and `1 ≤ q ^ 2`.
    ⚠️ **This is `PrimaryTower`'s own second branch with `pᵏ` replaced by `n`**, and it is the only
    part of that proof this file reuses.

⚠️ **`Finite (W.torsion n)` is read off the count** (`Nat.card ≠ 0`), not from a smoothness or
closure hypothesis, and `Finite (W.torsion q)` for `q ∣ n` follows from it by the inclusion
`E[q] ≤ E[n]` — which is where `finite_torsion_of_dvd` is spent and the only thing it is for.

## Main statements

* `WeierstrassCurve.Affine.nonempty_torsion_addEquiv_of_card`: `#E[n] = n²` forces
  `E[n] ≃+ ZMod n × ZMod n`, at every `n`, over any field with `(2 : F) ≠ 0` and `(n : F) ≠ 0`.
* `WeierstrassCurve.Affine.nonempty_torsion_addEquiv_of_splits_of_splits_Ψ₂Sq`: the same conclusion
  from the **three closure-free splitting conditions** of
  `EllipticCurves.Torsion.EvenTorsionCountSplits`' `card_torsion_eq_sq_of_splits_of_splits_Ψ₂Sq`,
  at every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0` and `[W.IsElliptic]`.

⚠️ **The hypothesis census, keyed on binders.**  Both public statements bind `(2 : F) ≠ 0` and
`(n : F) ≠ 0`; **only the second binds `[W.IsElliptic]`**, and it binds it because
`card_torsion_eq_sq_of_splits_of_splits_Ψ₂Sq` does — ⚠️ **the first takes no ellipticity instance at
all**, which is worth saying because every landed general-`n` structure statement does.  Both bind
`[DecidableEq F]`, from `W.Point`'s group structure and not from this file's content.  The five
`private` lemmas: two take neither characteristic condition, one takes a divisibility, one a
primality-and-non-divisibility and one `(n : F) ≠ 0` alone.

## ⚠️ What is *not* here

* ⚠️⚠️ **The CONVERSE, and the asymmetry is the whole reason this file is short.**  Nothing below
  derives `#E[n] = n²` from anything; the count is a hypothesis and `#2307`'s
  `card_torsion_eq_sq_of_splits_of_splits_Ψ₂Sq` is the only supplier cited.  **This file is a
  group-theoretic upgrade of a count, not an arithmetic theorem.**
* ⚠️ **Any widening of `nsmul_surjective_of_two_ne_zero`**, and it is **false** rather than
  unproved: `[n]` is not surjective on `E(F)` over a non-closed field — `E(ℚ)` at `n = 2` is the
  standard counterexample — so the `[IsAlgClosed F]` there is necessary and nothing below touches
  it.
* ⚠️ **Any widening of `nonempty_torsion_addEquiv_of_odd` (`PrimaryTowerOdd`) or of
  `nonempty_torsionTwoPow_addEquiv` (`TwoPrimary`).**  Both stay `[IsAlgClosed F]`-gated; this file
  supersedes them *for a caller who has the count*, and does not retire them, because they are
  stated without one.
* **The consumer at a division field.**  The statement a descent argument wants is the structure
  theorem over a finite Galois extension carrying full `n`-torsion, and the field is `#2327`'s
  `nDivisionField` / `nDivisionGaloisField`.  ⚠️ **That wiring is deliberately NOT here**: `#2327`
  is unreviewed at the time of writing, and coupling two unreviewed branches would make either one
  unlandable alone.  The three conditions this file's second statement takes are exactly the three
  `#2327` establishes over its tower and transports along an `F`-algebra map, so the wiring is two
  applications and no new mathematics.
* **Any statement about `E[n]` as a module** rather than as an additive group, and any `ZMod n`-
  linearity of the isomorphism.  `AddCommGroup.equiv_zmod_sq_of_card_sq` produces an `≃+` and
  nothing below sharpens it.
* **Characteristic `2`.**  Both statements carry `(2 : F) ≠ 0`.

## Recoveries

Three `example`s, all anonymous and all quoting their statements rather than referencing them:
the landed `[IsAlgClosed F]` form (which is what *subsumes* means here), the `n = 3` closure-free
member with `W.preΨ 3 = W.Ψ₃` discharged, and the `n = 2` member where ⚠️ **both `preΨ`-side
hypotheses are FREE** — `W.preΨ 2 = 1`, a unit splits and has no roots — leaving `W.Ψ₂Sq.Splits` as
the only surviving hypothesis.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6, Corollary 6.4.
-/

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

omit [DecidableEq F] in
/-- A prime dividing `n` is nonzero in `F` whenever `n` is. -/
private lemma natCast_prime_ne_zero_of_dvd {n q : ℕ} (hn : (n : F) ≠ 0) (hqn : q ∣ n) :
    (q : F) ≠ 0 := by
  intro hz
  obtain ⟨c, hc⟩ := hqn
  exact hn (by rw [hc]; push_cast; rw [hz, zero_mul])

/-- `E[q] ≤ E[n]` pointwise when `q ∣ n`. -/
private lemma nsmul_eq_zero_of_nsmul_eq_zero_of_dvd {n q : ℕ} (hqn : q ∣ n) {P : W.Point}
    (hP : q • P = 0) : n • P = 0 := by
  obtain ⟨c, hc⟩ := hqn
  rw [hc, mul_comm q c, ← smul_smul, hP, smul_zero]

/-- `E[q]` is finite whenever `E[n]` is and `q ∣ n`. -/
private lemma finite_torsion_of_dvd {n q : ℕ} (hqn : q ∣ n) [Finite (W.torsion n)] :
    Finite (W.torsion q) :=
  Finite.of_injective
    (fun a : W.torsion q => (⟨(a.1 : W.Point),
      mem_torsion_iff.mpr (nsmul_eq_zero_of_nsmul_eq_zero_of_dvd hqn
        (mem_torsion_iff.mp a.2))⟩ : W.torsion n))
    fun a b hab => Subtype.ext (by simpa using hab)

/-- The `q`-torsion of `E[n]` injects into `E[q]`. -/
private lemma card_nsmul_eq_zero_torsion_le {n q : ℕ} [Finite (W.torsion q)] :
    Nat.card {a : W.torsion n // q • a = 0} ≤ Nat.card (W.torsion q) := by
  refine Nat.card_le_card_of_injective
    (fun a => (⟨(a.1 : W.Point), mem_torsion_iff.mpr (congrArg Subtype.val a.2)⟩ :
      W.torsion q)) ?_
  intro a b hab
  simp only [Subtype.mk.injEq] at hab
  exact Subtype.ext (Subtype.ext hab)

/-- An element of `E[n]` killed by a prime `q` not dividing `n` is zero. -/
private lemma eq_zero_of_nsmul_eq_zero_of_not_dvd {n q : ℕ} (hq : q.Prime) (hqn : ¬ q ∣ n)
    (a : W.torsion n) (ha : q • a = 0) : a = 0 := by
  have hcop : IsCoprime (q : ℤ) (n : ℤ) := by
    have hnat : Nat.Coprime q n := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqn
    simpa using Nat.isCoprime_iff_coprime.mpr hnat
  obtain ⟨u, v, huv⟩ := hcop
  have hqa : (q : ℤ) • a = 0 := by
    rw [show (q : ℤ) = ((q : ℕ) : ℤ) from rfl, natCast_zsmul, ha]
  have hna : (n : ℤ) • a = 0 := by
    rw [show (n : ℤ) = ((n : ℕ) : ℤ) from rfl, natCast_zsmul]
    exact nsmul_mem_torsion a
  have h1 : ((1 : ℤ)) • a = 0 := by
    rw [← huv, add_smul, mul_smul, mul_smul, hqa, hna, smul_zero, smul_zero, add_zero]
  simpa using h1

/-- **`#E[n] = n²` forces `E[n] ≃+ ZMod n × ZMod n`**, over any field with `(2 : F) ≠ 0` and
`(n : F) ≠ 0`. -/
theorem nonempty_torsion_addEquiv_of_card (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : (n : F) ≠ 0)
    (hcard : Nat.card (W.torsion n) = n ^ 2) :
    Nonempty (W.torsion n ≃+ ZMod n × ZMod n) := by
  classical
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  haveI : Finite (W.torsion n) := by
    have h : Nat.card (W.torsion n) ≠ 0 := by rw [hcard]; exact pow_ne_zero 2 hn0
    exact (Nat.card_ne_zero.mp h).2
  refine AddCommGroup.equiv_zmod_sq_of_card_sq (Nat.pos_of_ne_zero hn0)
    (fun a => nsmul_mem_torsion a) hcard ?_
  intro q hq
  by_cases hqn : q ∣ n
  · haveI := finite_torsion_of_dvd (W := W) hqn
    exact card_nsmul_eq_zero_torsion_le.trans
      (card_torsion_le_sq h2 (natCast_prime_ne_zero_of_dvd hn hqn))
  · have hone : Nat.card {a : W.torsion n // q • a = 0} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨0, smul_zero q⟩⟩⟩
      rw [eq_zero_of_nsmul_eq_zero_of_not_dvd hq hqn a.1 a.2,
        eq_zero_of_nsmul_eq_zero_of_not_dvd hq hqn b.1 b.2]
    rw [hone]
    exact Nat.one_le_pow 2 q hq.pos

/-- **`E[n] ≃+ ZMod n × ZMod n` at every `n` from the THREE closure-free splitting conditions.** -/
theorem nonempty_torsion_addEquiv_of_splits_of_splits_Ψ₂Sq [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    {n : ℕ} (hn : (n : F) ≠ 0) (hsplits : (W.preΨ (n : ℤ)).Splits) (hsplits₂ : W.Ψ₂Sq.Splits)
    (hsq : ∀ x : F, (W.preΨ (n : ℤ)).eval x = 0 → IsSquare (W.Ψ₂Sq.eval x)) :
    Nonempty (W.torsion n ≃+ ZMod n × ZMod n) :=
  nonempty_torsion_addEquiv_of_card h2 hn
    (card_torsion_eq_sq_of_splits_of_splits_Ψ₂Sq h2 hn hsplits hsplits₂ hsq)

/-! ### Recoveries -/

/-- The landed `[IsAlgClosed F]`-gated structure theorem is an instance of the new one. -/
example [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : (n : F) ≠ 0) : Nonempty (W.torsion n ≃+ ZMod n × ZMod n) :=
  nonempty_torsion_addEquiv_of_card h2 hn (card_torsion_eq_sq h2 hn)

/-- The `n = 3` closure-free member. -/
example [W.IsElliptic] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hsplits : W.Ψ₃.Splits) (hsplits₂ : W.Ψ₂Sq.Splits)
    (hsq : ∀ x : F, W.Ψ₃.eval x = 0 → IsSquare (W.Ψ₂Sq.eval x)) :
    Nonempty (W.torsion 3 ≃+ ZMod 3 × ZMod 3) := by
  have h : W.preΨ ((3 : ℕ) : ℤ) = W.Ψ₃ := by
    rw [show (((3 : ℕ) : ℤ)) = (3 : ℤ) from rfl]
    simp [WeierstrassCurve.preΨ]
  exact nonempty_torsion_addEquiv_of_splits_of_splits_Ψ₂Sq h2 (by exact_mod_cast h3)
    (h ▸ hsplits) hsplits₂ fun x hx => hsq x (h ▸ hx)

/-- The `n = 2` closure-free member, where the `preΨ`-side hypotheses are free. -/
example [W.IsElliptic] (h2 : (2 : F) ≠ 0) (hsplits₂ : W.Ψ₂Sq.Splits) :
    Nonempty (W.torsion 2 ≃+ ZMod 2 × ZMod 2) := by
  have h : W.preΨ ((2 : ℕ) : ℤ) = 1 := by
    rw [show (((2 : ℕ) : ℤ)) = (2 : ℤ) from rfl]
    simp [WeierstrassCurve.preΨ]
  refine nonempty_torsion_addEquiv_of_splits_of_splits_Ψ₂Sq h2 (by exact_mod_cast h2)
    (h ▸ Polynomial.Splits.one) hsplits₂ fun x hx => ?_
  rw [h] at hx
  simp at hx

end WeierstrassCurve.Affine
