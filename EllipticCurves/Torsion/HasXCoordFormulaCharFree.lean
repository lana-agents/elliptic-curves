/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import EllipticCurves.Torsion.NsmulOrderCharFree

/-!
# `HasXCoordFormula W n` at every index with `(2 : F) ≠ 0` DELETED

`EllipticCurves.Torsion.NsmulOrder` proves the multiplication-by-`n` coordinate formula at **every**
index — `hasXCoordFormula_of_two_ne_zero` — over a field with `(2 : F) ≠ 0`, and reads
`[n]`-surjectivity off it in `nsmul_surjective_of_root`.  Of that file's eleven `h2`-binding
declarations, `EllipticCurves.Torsion.NsmulOrderCharFree` re-proved **seven** with no hypothesis on
`2`; the four it left are `divX_add_of_not_dvd`, `divX_add_mul_of_not_dvd`,
`hasXCoordFormula_of_two_ne_zero` and `nsmul_surjective_of_root`, and **this file is those four,
with `(2 : F) ≠ 0` deleted and nothing in its place.**

So the coordinate formula, and with it `[n]`-surjectivity on `E(F̄)`, now hold in characteristic `2`
as well.

## ⚠️⚠️ Why this is a third module and not an edit to either of the two below it

**`EllipticCurves.Torsion.NsmulOrder` is seven import edges BELOW the `ω` tower**, each edge a
single `import` line in the file on its left:

```
NsmulLadderOmegaStepDvd → NsmulLadderOmegaStepNum → NsmulLadderOmegaStep → NsmulLadderOmega
  → DoublingOmega → OmegaIntegral → NsmulYPeriodic → NsmulOrder
```

Adding `import EllipticCurves.Torsion.NsmulLadderOmegaStepDvd` to `NsmulOrder.lean` is therefore an
**import cycle**, exactly as it was for the order dictionary, so **the four landed signatures of
that file cannot move** — not as a matter of style, but because their proofs cannot reach an
`h2`-free ladder.  Nothing in `NsmulOrder.lean` is edited, weakened, restated or deprecated here,
and its blob is unmoved by this file.

⚠️ **`NsmulOrderCharFree.lean` could have carried these four and deliberately does not.**  Its own
module docstring says in terms that `HasXCoordFormula` is *not* generalised there and that the
generalisation needs a round which owns the naming question below; that clause stays true of that
file, and a separate module keeps the naming ruling, the four new statements and the
characteristic-`2` exhibit in one place a reader can audit on its own.

## ⚠️⚠️ The naming ruling, which is the whole non-mathematical cost of this file

**`hasXCoordFormula_of_two_ne_zero` carries its hypothesis in its NAME, and the name is cited
across the tree.**  Three shapes were available and this file takes the third:

* ⛔ **Delete `h2` and keep the name.**  The name would then read `_of_two_ne_zero` with no such
  binder — false in the name itself — and a vestigial binder is not available either: `lake lint`'s
  `unusedArguments` tests theorems as well as definitions and exempts only binders whose name begins
  with `_`.
* ⛔ **Rename the landed theorem to `hasXCoordFormula`.**  Every citation of the old name would
  resolve nowhere, which is strictly worse than leaving prose understated.
* ✅ **Add the unconditional statement beside the landed one, under the unsuffixed name
  `hasXCoordFormula`, and leave the landed name and signature exactly as they are.**  Every existing
  citation still resolves, no call site changes, and the new name says what it proves.  ⚠️ The same
  ruling gives `divX_add_of_not_dvd'`, `divX_add_mul_of_not_dvd'` and `nsmul_surjective_of_root'`
  their primes, which is `NsmulOrderCharFree`'s and `NsmulLadderOmegaStepDvd`'s installed convention
  for a landed unprimed name.

⚠️ **What the ruling leaves SHORT rather than FALSE, said rather than left unsaid**: the docstrings
that cite `hasXCoordFormula_of_two_ne_zero` as holding *"at every index with `(2 : F) ≠ 0`"* remain
true — a theorem that needs no hypothesis is in particular available when one holds — so no
existing sentence becomes false and none is edited by this file.  **No rename sweep is performed.**

## What is reached from below rather than re-proved

Nothing in this file re-proves a landed statement.  Four of
`EllipticCurves.Torsion.NsmulOrderCharFree`'s primed declarations are consumed as they stand —
`nsmul_eq_zero_of_minimal_ψ_evalEval_eq_zero'`, `ψ_evalEval_ne_zero_of_not_dvd'`,
`ψ_evalEval_eq_zero_of_dvd'` and `nsmul_eq_zero_iff_ψ_evalEval_eq_zero'` — and ⚠️ **they are not
all that file declares**: no count of its primed set is given here, and the ones this file does not
consume it does not name in prose either.  So are `EllipticCurves.Torsion.NsmulOrder`'s
`ψ_evalEval_eq_zero_of_ψ_two_evalEval_eq_zero`, `ψ_shift_step_of_ψ_eq_zero` and
`exists_minimal_ψ_evalEval_eq_zero`, which bind no `h2`.

## The one substitution the coordinate formula needs that the dictionary did not

`EllipticCurves.Torsion.NsmulLadder`'s `nsmul_eq_some_Φ_div_ΨSq` is where
`hasXCoordFormula_of_two_ne_zero` spends two of its six `h2` uses, and its `h2`-free replacement
is `EllipticCurves.Torsion.NsmulLadderOmegaStepDvd`'s `nsmul_eq_some_divX_divYω`, which is
**strictly stronger**: it names the `y`-coordinate as `ωNumₙ/ψₙ³` instead of leaving it
existential, so the only change at the call sites is that the witness is produced rather than
destructured.  The other four uses are `nsmul_eq_zero_of_minimal_ψ_evalEval_eq_zero` (twice),
`ψ_evalEval_eq_zero_of_dvd` and `divX_add_mul_of_not_dvd`, the first two primed in
`NsmulOrderCharFree` and the third proved here.

⚠️ **The `2`-torsion branch of the coordinate formula was already `h2`-free in content**: it runs on
`ψ_evalEval_eq_zero_of_ψ_two_evalEval_eq_zero`, a parity argument and `Φ_eval_eq_of_equation`, and
its one `h2` is the `d = 2` instance of `nsmul_eq_zero_of_minimal_ψ_evalEval_eq_zero`.  **So this
file inherits no `ht : ψ₂(x, y) ≠ 0`** — which is the asymmetry between this lane and the order
dictionary, whose `ht` is sharp.

## Main statements

* `WeierstrassCurve.Affine.hasXCoordFormula` : ⚠️⚠️ **`HasXCoordFormula W n` at every index `n`
  over EVERY field**, with no hypothesis on `2` and no hypothesis on the point.
* `WeierstrassCurve.Affine.nsmul_surjective_of_root'` : **`[n]`-surjectivity on `E(F̄)` with
  `(2 : F) ≠ 0` deleted**, at every `n ≠ 0` whose `Φₙ` and `ΨSqₙ` have no common root.  ⚠️ `hroot`
  is **not** discharged here; that is `#1184` and it stays open.
* `WeierstrassCurve.Affine.divX_add_of_not_dvd'` and
  `WeierstrassCurve.Affine.divX_add_mul_of_not_dvd'` : the `d`-periodicity of `Φₙ/ΨSqₙ` off the
  multiples of the order, with no hypothesis on `2`.
* `WeierstrassCurve.Affine.hasXCoordFormula_five_curveCharTwoOne` and
  `WeierstrassCurve.Affine.not_forall_ψ_ne_zero_five_curveCharTwoOne` : ⚠️ **the
  characteristic-`2` payoff as a STRICT extension of the ladder, exhibited and not asserted.**  On
  `y² + xy = x³ + 1` over `ZMod 2` the point `(1, 0)` has order `4`, so at `n = 5` the ladder passes
  through the zero `ψ₄(1, 0) = 0` and `nsmul_eq_some_divX_divYω` is unavailable, while
  `ΨSq₅(1) ≠ 0` and the coordinate formula gives `5 • (1, 0)` an affine `x`-coordinate anyway.

## ⚠️ What this file does NOT do

* ⚠️ **No rename and no citation sweep.**  `hasXCoordFormula_of_two_ne_zero` and
  `nsmul_surjective_of_root` keep their names, their signatures and all their call sites; this file
  only adds names.
* ⚠️ **`hroot` is not discharged** — see `#1184`.  `nsmul_surjective_of_root'` has exactly the
  hypotheses of `nsmul_surjective_of_root` minus `h2`.
* ⚠️ **No `h2` is removed anywhere else.**  The `h2` uses of
  `EllipticCurves.Torsion.TwoTorsionOrder`, `EllipticCurves.Torsion.NsmulYPeriodic`,
  `EllipticCurves.Torsion.ChordSum`, `EllipticCurves.Torsion.XSupport`,
  `EllipticCurves.Torsion.NthPartSeparable`, `EllipticCurves.Torsion.TriplingSeparable` and
  `EllipticCurves.FunctionField.MulByNXCoordFormula` are untouched, and this file is imported
  by nothing but the root aggregator.
* ⚠️ **No statement about the Tate module — but this file is ON the path of the rows that want
  one, and this bullet must not be read as denying that.**  `#2340` items 4 and 5 are
  `EllipticCurves.TateModule.FreeGeneral`'s four CONCLUSION statements —
  `nonempty_tateModuleEquivProd_of_natCast_ne_zero`, `free_tateModule_of_natCast_ne_zero`,
  `finrank_tateModule_of_natCast_ne_zero` and `finite_tateModule_of_natCast_ne_zero` — and each of
  them takes a count **and** a basis.  ⚠️ **Those four are named here rather than counted off the
  `…_of_natCast_ne_zero` suffix**, which that file carries on more declarations than these four —
  the count and the basis themselves among them.  The basis leg
  `exists_compatible_basis_of_natCast_ne_zero` has **three** `h2` sources:
  `nsmul_surjective_of_root`, generalised here as `nsmul_surjective_of_root'`;
  `eval_Φ_ne_zero_of_eval_ΨSq_eq_zero`, which is `hroot` and `#1184`'s; and
  `nonempty_torsion_addEquiv`, reached through `exists_closure_pair_eq_torsion`.  ⚠️ **So the
  obstruction remaining on this file's leg is `hroot` and not the characteristic.**  No module of
  `EllipticCurves.TateModule` imports `EllipticCurves.Torsion.NsmulOrderCharFree` at all, so the
  order dictionary is not what those rows consume either.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and Exercise 3.7.
* M. Ward, *Memoir on elliptic divisibility sequences*, Amer. J. Math. **70** (1948).
-/

open Polynomial Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-! ## `d`-periodicity of the predicted `x`-coordinate, with no hypothesis on `2` -/

section Periodicity

/-- **One period of the predicted `x`-coordinate**, with `(2 : F) ≠ 0` deleted —
`EllipticCurves.Torsion.NsmulOrder`'s `divX_add_of_not_dvd`.

Ward's relation at `(m + d, m, 1, 0)` says exactly that `ψ_{m+1}ψ_{m−1}/ψₘ²` is unchanged by
`m ↦ m + d`, and that quotient is `x − Φₘ/ΨSqₘ`.  ⚠️ **The whole `h2` of the landed proof is its
`ψ_evalEval_ne_zero_of_not_dvd`**, which `EllipticCurves.Torsion.NsmulOrderCharFree` has already
re-proved as `ψ_evalEval_ne_zero_of_not_dvd'`; the Ward step `ψ_shift_step_of_ψ_eq_zero` and
`sub_Φ_div_ΨSq` bind none. -/
theorem divX_add_of_not_dvd' (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y ≠ 0) {e : ℕ}
    (hd : (W.ψ ((e : ℤ) + 3)).evalEval x y = 0)
    (hmin : ∀ k : ℤ, 1 ≤ k → k < (e : ℤ) + 3 → (W.ψ k).evalEval x y ≠ 0)
    (m : ℕ) (hm : ¬ ((e + 3) ∣ m)) :
    W.divX x ((m : ℤ) + ((e : ℤ) + 3)) = W.divX x (m : ℤ) := by
  have hnd := ψ_evalEval_ne_zero_of_not_dvd' hns ht hd hmin
  have hA : (W.ψ (m : ℤ)).evalEval x y ≠ 0 := hnd m hm
  have hB : (W.ψ ((m : ℤ) + ((e : ℤ) + 3))).evalEval x y ≠ 0 := by
    have hnd1 := hnd (m + (e + 3)) (fun hdv =>
      hm ((Nat.dvd_add_iff_left (dvd_refl (e + 3))).mpr hdv))
    rwa [show (((m + (e + 3) : ℕ)) : ℤ) = (m : ℤ) + ((e : ℤ) + 3) by push_cast; ring] at hnd1
  have hlow := sub_Φ_div_ΨSq (W := W) (y := y) hns.left (n := (m : ℤ)) hA
  have hhigh := sub_Φ_div_ΨSq (W := W) (y := y) hns.left (n := (m : ℤ) + ((e : ℤ) + 3)) hB
  have hstep := ψ_shift_step_of_ψ_eq_zero hd (m : ℤ)
  have hEq : (W.ψ ((m : ℤ) + ((e : ℤ) + 3) + 1)).evalEval x y *
        (W.ψ ((m : ℤ) + ((e : ℤ) + 3) - 1)).evalEval x y /
        (W.ψ ((m : ℤ) + ((e : ℤ) + 3))).evalEval x y ^ 2 =
      (W.ψ ((m : ℤ) + 1)).evalEval x y * (W.ψ ((m : ℤ) - 1)).evalEval x y /
        (W.ψ (m : ℤ)).evalEval x y ^ 2 := by
    rw [div_eq_div_iff (pow_ne_zero 2 hB) (pow_ne_zero 2 hA)]
    linear_combination hstep
  simp only [divX]
  linear_combination -(hhigh.trans (hEq.trans hlow.symm))

/-- **The predicted `x`-coordinate is periodic with period `d` off the multiples of `d`**, with
`(2 : F) ≠ 0` deleted — `EllipticCurves.Torsion.NsmulOrder`'s `divX_add_mul_of_not_dvd`. -/
theorem divX_add_mul_of_not_dvd' (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y ≠ 0) {e : ℕ}
    (hd : (W.ψ ((e : ℤ) + 3)).evalEval x y = 0)
    (hmin : ∀ k : ℤ, 1 ≤ k → k < (e : ℤ) + 3 → (W.ψ k).evalEval x y ≠ 0)
    (j : ℕ) (hj : ¬ ((e + 3) ∣ j)) :
    ∀ q : ℕ, W.divX x ((j : ℤ) + q * ((e : ℤ) + 3)) = W.divX x (j : ℤ) := by
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
    have hnj : ¬ ((e + 3) ∣ (j + q * (e + 3))) := fun hdv =>
      hj ((Nat.dvd_add_iff_left (dvd_mul_left (e + 3) q)).mpr hdv)
    have := divX_add_of_not_dvd' hns ht hd hmin (j + q * (e + 3)) hnj
    rw [show (((j + q * (e + 3) : ℕ)) : ℤ) = (j : ℤ) + q * ((e : ℤ) + 3) by push_cast; ring] at this
    rw [show (j : ℤ) + ((q : ℕ) + 1 : ℕ) * ((e : ℤ) + 3)
        = (j : ℤ) + q * ((e : ℤ) + 3) + ((e : ℤ) + 3) by push_cast; ring, this, ih]

end Periodicity

/-! ## The coordinate formula at every index, with no hypothesis on `2` -/

section Formula

variable [DecidableEq F]

/-- ⚠️⚠️ **`WeierstrassCurve.Affine.HasXCoordFormula W n` AT EVERY INDEX OVER EVERY FIELD** —
`EllipticCurves.Torsion.NsmulOrder`'s `hasXCoordFormula_of_two_ne_zero` with `(2 : F) ≠ 0` deleted
and nothing in its place, so in particular in characteristic `2`.

This is `#251`'s scope item 1 with both the ladder hypothesis and the characteristic hypothesis
removed, and it is the index-dependent input of the `[n]`-surjectivity engine.

⚠️ **The landed name and signature do not move**, and `hasXCoordFormula_of_two_ne_zero` is not
deprecated: see the module docstring for why the unsuffixed name is the one taken here.

⚠️ **The three branches spend the characteristic in three different landed theorems, all of them
now available unconditionally**: the `2`-torsion branch in the `d = 2` instance of
`nsmul_eq_zero_of_minimal_ψ_evalEval_eq_zero'`, the no-zero branch in `nsmul_eq_some_divX_divYω`
(where the `y`-coordinate is the unhalved `ωNumₙ/ψₙ³` and not `divY`), and the branch with a zero in
`ψ_evalEval_eq_zero_of_dvd'` and `divX_add_mul_of_not_dvd'`. -/
theorem hasXCoordFormula (n : ℕ) : HasXCoordFormula W n := by
  classical
  intro x y hns hΨ
  have hψn : (W.ψ (n : ℤ)).evalEval x y ≠ 0 := fun h =>
    hΨ (by rw [← ψ_sq_evalEval hns.left, h]; ring)
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (by simp) hψn
    · exact h
  by_cases ht : (W.ψ 2).evalEval x y = 0
  · -- `(x, y)` is a `2`-torsion point: `n` is odd, `n • (x, y) = (x, y)` and `Φₙ/ΨSqₙ = x`.
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := by
      rcases Nat.even_or_odd n with ⟨m, hm⟩ | hodd
      · refine absurd ?_ hψn
        have hcast : ((n : ℤ)) = 2 * (m : ℤ) := by rw [hm]; push_cast; ring
        rw [hcast]
        exact ψ_evalEval_eq_zero_of_ψ_two_evalEval_eq_zero ht m
      · obtain ⟨m, hm⟩ := hodd
        exact ⟨m, hm⟩
    have htwo : ((2 : ℕ) • Point.some x y hns : W.Point) = 0 :=
      nsmul_eq_zero_of_minimal_ψ_evalEval_eq_zero' hns (by omega)
        (by rw [Nat.cast_ofNat]; exact ht)
        (fun k hk1 hk2 => by
          rw [show k = 1 by omega, ψ_one_evalEval]; exact one_ne_zero)
    have hnP : ((2 * m + 1 : ℕ) • Point.some x y hns : W.Point) = Point.some x y hns := by
      rw [add_nsmul, mul_comm, ← smul_smul, htwo, smul_zero, one_nsmul, zero_add]
    have hup : (W.ψ (((2 * m + 1 : ℕ) : ℤ) + 1)).evalEval x y = 0 := by
      rw [show (((2 * m + 1 : ℕ) : ℤ) + 1) = 2 * ((m : ℤ) + 1) by push_cast; ring]
      exact ψ_evalEval_eq_zero_of_ψ_two_evalEval_eq_zero ht _
    have hdown : (W.ψ (((2 * m + 1 : ℕ) : ℤ) - 1)).evalEval x y = 0 := by
      rw [show (((2 * m + 1 : ℕ) : ℤ) - 1) = 2 * (m : ℤ) by push_cast; ring]
      exact ψ_evalEval_eq_zero_of_ψ_two_evalEval_eq_zero ht _
    have hXx : (W.Φ ((2 * m + 1 : ℕ) : ℤ)).eval x / (W.ΨSq ((2 * m + 1 : ℕ) : ℤ)).eval x = x := by
      rw [Φ_eval_eq_of_equation hns.left, hup, hdown, ← ψ_sq_evalEval hns.left]
      field_simp
      ring
    rw [hXx]
    exact ⟨y, hns, hnP⟩
  · -- `(x, y)` is not `2`-torsion.
    by_cases hall : ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) → (W.ψ k).evalEval x y ≠ 0
    · obtain ⟨h', heq⟩ := nsmul_eq_some_divX_divYω hns hn1 hall
      exact ⟨_, h', heq⟩
    · push Not at hall
      obtain ⟨k₀, hk₀1, -, hk₀⟩ := hall
      obtain ⟨e, hd0, hmin'⟩ := exists_minimal_ψ_evalEval_eq_zero ht
        ⟨k₀.toNat, by omega, by rwa [Int.toNat_of_nonneg (by omega)]⟩
      have hcastd : (((e + 3 : ℕ)) : ℤ) = (e : ℤ) + 3 := by push_cast; ring
      have hdvd := ψ_evalEval_eq_zero_of_dvd' hns ht hd0 hmin'
      have hnotdvd : ¬ ((e + 3) ∣ n) := fun h => hψn (hdvd n h)
      obtain ⟨j, q, hn, hj0, hjlt⟩ :
          ∃ j q : ℕ, n = j + q * (e + 3) ∧ j ≠ 0 ∧ j < e + 3 :=
        ⟨n % (e + 3), n / (e + 3), (Nat.mod_add_div' n (e + 3)).symm,
          fun h => hnotdvd (Nat.dvd_of_mod_eq_zero h), Nat.mod_lt _ (by omega)⟩
      have hnotdvdj : ¬ ((e + 3) ∣ j) := fun h => by
        have := Nat.le_of_dvd (by omega) h; omega
      have hjne : ∀ k : ℤ, 1 ≤ k → k ≤ (j : ℤ) → (W.ψ k).evalEval x y ≠ 0 := by
        intro k hk1 hk2
        exact hmin' k hk1 (by omega)
      obtain ⟨h', hjP⟩ := nsmul_eq_some_divX_divYω hns (by omega) hjne
      have hzero : ((e + 3 : ℕ) • Point.some x y hns : W.Point) = 0 :=
        nsmul_eq_zero_of_minimal_ψ_evalEval_eq_zero' hns (by omega)
          (by rw [hcastd]; exact hd0) (fun k hk1 hk2 => hmin' k hk1 (by rwa [hcastd] at hk2))
      have hqz : ∀ r : ℕ, ((r * (e + 3) : ℕ) • Point.some x y hns : W.Point) = 0 := by
        intro r
        induction r with
        | zero => simp
        | succ r ihr =>
          rw [show (r + 1) * (e + 3) = r * (e + 3) + (e + 3) by ring, add_nsmul, ihr, hzero,
            add_zero]
      have hnP : ((n : ℕ) • Point.some x y hns : W.Point) = j • Point.some x y hns := by
        conv_lhs => rw [hn]
        rw [add_nsmul, hqz q, add_zero]
      have hXX : (W.Φ (n : ℤ)).eval x / (W.ΨSq (n : ℤ)).eval x
          = (W.Φ (j : ℤ)).eval x / (W.ΨSq (j : ℤ)).eval x := by
        have hper := divX_add_mul_of_not_dvd' hns ht hd0 hmin' j hnotdvdj q
        rw [show (j : ℤ) + (q : ℤ) * ((e : ℤ) + 3) = (n : ℤ) by rw [hn]; push_cast; ring] at hper
        simpa only [divX] using hper
      rw [hXX]
      exact ⟨_, h', by rw [hnP]; exact hjP⟩

/-! ## The payoff: `[n]`-surjectivity with no hypothesis on `2` -/

/-- ⚠️⚠️ **MULTIPLICATION BY `n` IS SURJECTIVE ON `E(F̄)` AT EVERY `n ≠ 0` WHOSE `Φₙ` AND `ΨSqₙ`
HAVE NO COMMON ROOT, WITH NO HYPOTHESIS ON `2`** — `EllipticCurves.Torsion.NsmulOrder`'s
`nsmul_surjective_of_root` with `h2` deleted.

⚠️ **One application and no new mathematics**: `nsmul_surjective_of_hasXCoordFormula` binds no `h2`
as of `#2253`, so `nsmul_surjective_of_root`'s binder had exactly one source, the coordinate
formula, and `hasXCoordFormula` above removes it.

⚠️ **`hroot` is NOT discharged here.**  It is the weakening of `#1184` recorded there, and this
statement's hypotheses are the landed ones minus `h2` and nothing else. -/
theorem nsmul_surjective_of_root' [IsAlgClosed F] [W.IsElliptic] {n : ℕ}
    (hn : n ≠ 0) (hroot : ∀ x : F, (W.ΨSq n).eval x = 0 → (W.Φ n).eval x ≠ 0) :
    Function.Surjective fun P : W.Point => n • P :=
  nsmul_surjective_of_hasXCoordFormula hn hroot (hasXCoordFormula n)

/-! ## ⚠️ Characteristic `2`, and a STRICT extension of the ladder -/

section CharTwo

/-- **`ψ₅(1, 0) ≠ 0` on `curveCharTwoOne = ⟨1, 0, 0, 0, 1⟩` over `ZMod 2`**, read off the order of
the point and not computed: `(1, 0)` has order `4` and `4 ∤ 5`. -/
theorem ψ_five_evalEval_ne_zero_curveCharTwoOne :
    (curveCharTwoOne.ψ ((5 : ℕ) : ℤ)).evalEval 1 0 ≠ 0 := fun h =>
  absurd ((nsmul_eq_zero_iff_four_dvd_curveCharTwoOne 5).mp
      ((nsmul_eq_zero_iff_ψ_evalEval_eq_zero' nonsingular_curveCharTwoOne
        (by rw [evalEval_ψ_two_curveCharTwoOne]; exact one_ne_zero) 5).mpr h))
    (by decide)

/-- **`ΨSq₅(1) ≠ 0` on `curveCharTwoOne`** — `ΨSq₅(1) = ψ₅(1, 0)²`. -/
theorem ΨSq_five_eval_ne_zero_curveCharTwoOne :
    (curveCharTwoOne.ΨSq ((5 : ℕ) : ℤ)).eval 1 ≠ 0 := by
  rw [← ψ_sq_evalEval equation_curveCharTwoOne]
  exact pow_ne_zero 2 ψ_five_evalEval_ne_zero_curveCharTwoOne

/-- ⚠️⚠️ **THE LADDER AT `n = 5` PASSES THROUGH A ZERO ON `curveCharTwoOne`**: `ψ₄(1, 0) = 0`, so
the hypothesis of `EllipticCurves.Torsion.NsmulLadderOmegaStepDvd`'s `nsmul_eq_some_divX_divYω` —
and of every ladder theorem of this tree — is **false** at `(1, 0)` and `n = 5`.

⚠️ This is the cell that makes the exhibit below a strict extension rather than a restatement: the
coordinate formula is available at an index where the ladder is not. -/
theorem not_forall_ψ_ne_zero_five_curveCharTwoOne :
    ¬ ∀ k : ℤ, 1 ≤ k → k ≤ ((5 : ℕ) : ℤ) → (curveCharTwoOne.ψ k).evalEval 1 0 ≠ 0 := fun h =>
  h 4 (by norm_num) (by norm_num) ψ_four_evalEval_curveCharTwoOne

/-- ⚠️⚠️ **THE COORDINATE FORMULA IN CHARACTERISTIC `2`, AT AN INDEX THE LADDER CANNOT REACH**: on
`y² + xy = x³ + 1` over `ZMod 2`, `5 • (1, 0)` is affine with `x`-coordinate `Φ₅(1)/ΨSq₅(1)`.

⚠️ **Every hypothesis of this is a landed theorem rather than an assertion**: `ΨSq₅(1) ≠ 0` comes
from the order of `(1, 0)` being `4` (`nsmul_eq_zero_iff_four_dvd_curveCharTwoOne`, itself read off
`ψ` alone), and `(2 : ZMod 2) = 0` holds, so `hasXCoordFormula_of_two_ne_zero` produces **nothing**
here — its hypothesis is false over this field.

⚠️ **And the ladder produces nothing either**, by `not_forall_ψ_ne_zero_five_curveCharTwoOne`:
`ψ₄(1, 0) = 0`.  So this statement is reachable by `hasXCoordFormula` and by no other theorem of
this tree. -/
theorem hasXCoordFormula_five_curveCharTwoOne :
    ∃ (y' : ZMod 2) (h' : curveCharTwoOne.Nonsingular
        ((curveCharTwoOne.Φ ((5 : ℕ) : ℤ)).eval 1 / (curveCharTwoOne.ΨSq ((5 : ℕ) : ℤ)).eval 1) y'),
      ((5 : ℕ) • (Point.some 1 0 nonsingular_curveCharTwoOne : curveCharTwoOne.Point))
        = .some _ y' h' :=
  hasXCoordFormula 5 nonsingular_curveCharTwoOne ΨSq_five_eval_ne_zero_curveCharTwoOne

end CharTwo

end Formula

end WeierstrassCurve.Affine
