/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.HasXCoordFormulaCharFree
import EllipticCurves.Torsion.TwoTorsionOrder

/-!
# `[n]`-surjectivity on `E(F̄)` with `(2 : F) ≠ 0` deleted and no `hroot`

`EllipticCurves.Torsion.TwoTorsionOrder` proves that multiplication by `n` is surjective on
`E(F̄)` at every `n ≠ 0` — `nsmul_surjective_of_two_ne_zero` — over an algebraically closed field
with `(2 : F) ≠ 0` on an elliptic curve, and that is the statement
`EllipticCurves.TateModule.FreeGeneral` and its neighbours reach for when they want a surjection.
**This file is that statement with `(2 : F) ≠ 0` deleted and nothing in its place**, together with
the declarations beneath it that the deletion goes through.

`nsmul_surjective_of_two_ne_zero`'s body spends its hypothesis in exactly two places —
`nsmul_surjective_of_root` and `eval_Φ_ne_zero_of_eval_ΨSq_eq_zero` — and
`EllipticCurves.Torsion.HasXCoordFormulaCharFree` has already killed the first, as
`nsmul_surjective_of_root'`.  **The second one is this file.**  It funnels, in turn, through a
single declaration, `eval_ΨSq_adjacent_ne_zero_of_eval_ΨSq_eq_zero`, whose own `h2` is spent at
four sites.  One of them already has a hypothesis-free counterpart on the page: `exists_equation'`
(`EllipticCurves.Torsion.ThreeTorsionStructure`) produces a point above an arbitrary `x` whatever
the characteristic.  **The other three get theirs below** —
`nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic'`,
`ψ_add_one_evalEval_ne_zero_of_nsmul_eq_zero'` and
`ψ_sub_one_evalEval_ne_zero_of_nsmul_eq_zero'` — which is why this file declares those three
rather than citing them, and the dictionary they are read through is
`EllipticCurves.Torsion.NsmulOrderCharFree`'s `nsmul_eq_zero_iff_ψ_evalEval_eq_zero'`, away from
`2`-torsion.  So the mathematics here is a substitution and a case split, and the file is short on
purpose.

## ⚠️⚠️ Why this is a new module and not an edit to `EllipticCurves.Torsion.TwoTorsionOrder`

For the reason `EllipticCurves.Torsion.NsmulOrderCharFree` is not an edit to
`EllipticCurves.Torsion.NsmulOrder`: **`Torsion.TwoTorsionOrder` sits below the `ω` tower and
cannot see the `h2`-free dictionary at all.**  It imports `Torsion.NsmulOrder`, which is seven
`import` edges below the `ω` tower — the figure `Torsion.HasXCoordFormulaCharFree` and
`Torsion.NsmulOrderCharFree` both state, at the same upper endpoint
`Torsion.NsmulLadderOmegaStepDvd` — so putting the generalisation in that file is a cycle and not
a choice of style.

**A new module above both is not a cycle, and the membership is measured rather than assumed.**
Walking the `^import EllipticCurves…` lines transitively from each root, with the module itself
**not** counted — the convention `## Import-closure figures` states — at commit `6ab5647b`:

* `Torsion.HasXCoordFormulaCharFree` reaches **45** modules, and `Torsion.TwoTorsionOrder` is
  **not** one of them.
* `Torsion.TwoTorsionOrder` reaches **25**, and `Torsion.HasXCoordFormulaCharFree` is **not** one
  of them.
* `Torsion.ThreeTorsionStructure`, which is where `exists_equation'` lives, is in **both** of those
  closures, so the `h2`-free point-existence lemma is free from either side.

⚠️ Both counts are keyed because they are counts over the tree and move under any landing upstream;
the two **memberships** are what the acyclicity rests on and they are not counts.

## Main statements

⚠️ **Every statement below is the identically-named declaration of
`EllipticCurves.Torsion.TwoTorsionOrder` with `(2 : F) ≠ 0` deleted and nothing put in its place;
the bullets name the conclusions, and `[DecidableEq F]`, `[IsAlgClosed F]` and `[W.IsElliptic]` are
in the signatures where the landed forms carry them.**

* `WeierstrassCurve.Affine.nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic'` : the order
  dictionary `n • P = 0 ↔ ψₙ(P) = 0` at **every** point of an elliptic curve, `2`-torsion
  included.
* `WeierstrassCurve.Affine.ψ_add_one_evalEval_ne_zero_of_nsmul_eq_zero'` and
  `WeierstrassCurve.Affine.ψ_sub_one_evalEval_ne_zero_of_nsmul_eq_zero'` : the neighbours of a
  killing index do not vanish.
* `WeierstrassCurve.Affine.eval_ΨSq_adjacent_ne_zero_of_eval_ΨSq_eq_zero'` : at a root of `ΨSqₙ`
  neither neighbour `ΨSq_{n±1}` vanishes.
* `WeierstrassCurve.Affine.eval_Φ_ne_zero_of_eval_ΨSq_eq_zero'` : `Φₙ` and `ΨSqₙ` have no common
  root — the `hroot` of `nsmul_surjective_of_root'`, discharged.
* `WeierstrassCurve.Affine.nsmul_surjective` : **`[n]` is surjective on `E(F̄)` at every `n ≠ 0`**,
  over an algebraically closed field, on an elliptic curve, with no hypothesis on `2` and no
  `hroot`.

## ⚠️ What is *not* reached here

⚠️ **`#1184` does not move.**  `hroot` is discharged over an **algebraically closed** field, by
lifting a root of `ΨSqₙ` to a point of `W`; the open statement is
`IsCoprime (ΨSq_{n+1} · ΨSq_{n−1}) (ΨSq n)` over an arbitrary commutative ring, and nothing here
touches it.  ⚠️ `nsmul_surjective_of_root'` keeps its `hroot` and is not restated.

⚠️ **The landed `nsmul_surjective_of_two_ne_zero` keeps its name, and so do
`nsmul_surjective_of_root` and `hasXCoordFormula_of_two_ne_zero`.**  Nothing is renamed and nothing
is deprecated: every `EllipticCurves.TateModule` docstring that cites
`nsmul_surjective_of_two_ne_zero` by name, and every use of it in code, resolves exactly as
before.  What this file adds is a statement beside it.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and Exercise 3.7.
-/

open Polynomial Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-! ## The order dictionary at every point, with no hypothesis on `2` -/

section Point

variable [DecidableEq F] [W.IsElliptic]

/-- **`n • (x, y) = 0 ↔ ψₙ(x, y) = 0` at every point, with no hypothesis on `2`** —
`EllipticCurves.Torsion.TwoTorsionOrder`'s `nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic`
with `(2 : F) ≠ 0` deleted and nothing in its place.

The case split is the landed one and the `2`-torsion branch is unchanged: there
`nsmul_eq_zero_iff_two_dvd_of_ψ_two_evalEval_eq_zero` and
`ψ_three_evalEval_ne_zero_of_ψ_two_evalEval_eq_zero` already bind no hypothesis on `2`, so the
whole of the deletion is in the other branch, where
`EllipticCurves.Torsion.NsmulOrderCharFree`'s `nsmul_eq_zero_iff_ψ_evalEval_eq_zero'` replaces
`nsmul_eq_zero_iff_ψ_evalEval_eq_zero`. -/
theorem nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic' (hns : W.Nonsingular x y) (n : ℕ) :
    ((n • Point.some x y hns : W.Point) = 0) ↔ (W.ψ (n : ℤ)).evalEval x y = 0 := by
  by_cases ht : (W.ψ 2).evalEval x y = 0
  · have h := nsmul_eq_zero_iff_two_dvd_of_ψ_two_evalEval_eq_zero hns ht
      (ψ_three_evalEval_ne_zero_of_ψ_two_evalEval_eq_zero hns.left ht) n
    exact h.1.trans h.2.symm
  · exact nsmul_eq_zero_iff_ψ_evalEval_eq_zero' hns ht n

/-- **`ψ_{n+1}(x, y) ≠ 0` when `n` kills the point, with no hypothesis on `2`** —
`EllipticCurves.Torsion.TwoTorsionOrder`'s `ψ_add_one_evalEval_ne_zero_of_nsmul_eq_zero` with
`(2 : F) ≠ 0` deleted.  Same argument, read through the dictionary above: if `ψ_{n+1}` vanished
then `(n + 1) • P` would be `0` alongside `n • P`, and their difference is `P`. -/
theorem ψ_add_one_evalEval_ne_zero_of_nsmul_eq_zero' (hns : W.Nonsingular x y) {n : ℕ}
    (hz : (n • Point.some x y hns : W.Point) = 0) :
    (W.ψ ((n : ℤ) + 1)).evalEval x y ≠ 0 := by
  intro hcon
  have hsucc : ((n + 1 : ℕ) • Point.some x y hns : W.Point) = 0 := by
    refine (nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic' hns (n + 1)).mpr ?_
    rwa [show (((n + 1 : ℕ)) : ℤ) = (n : ℤ) + 1 by push_cast; ring]
  rw [succ_nsmul, hz, zero_add] at hsucc
  exact Point.some_ne_zero hns hsucc

/-- **`ψ_{n−1}(x, y) ≠ 0` when `n ≠ 0` kills the point, with no hypothesis on `2`** —
`EllipticCurves.Torsion.TwoTorsionOrder`'s `ψ_sub_one_evalEval_ne_zero_of_nsmul_eq_zero` with
`(2 : F) ≠ 0` deleted.  Same argument as
`ψ_add_one_evalEval_ne_zero_of_nsmul_eq_zero'`, read at `n − 1`. -/
theorem ψ_sub_one_evalEval_ne_zero_of_nsmul_eq_zero' (hns : W.Nonsingular x y) {n : ℕ}
    (hn : n ≠ 0) (hz : (n • Point.some x y hns : W.Point) = 0) :
    (W.ψ ((n : ℤ) - 1)).evalEval x y ≠ 0 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
  intro hcon
  have hpred : ((k : ℕ) • Point.some x y hns : W.Point) = 0 := by
    refine (nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic' hns k).mpr ?_
    rwa [show ((k : ℕ) : ℤ) = (((k + 1 : ℕ)) : ℤ) - 1 by push_cast; ring]
  rw [succ_nsmul, hpred, zero_add] at hz
  exact Point.some_ne_zero hns hz

end Point

/-! ## The payoff: `hroot` is a theorem in every characteristic -/

/-- **At a root of `ΨSqₙ`, neither neighbour `ΨSq_{n±1}` vanishes**, over an algebraically closed
field on an elliptic curve, with no hypothesis on `2` —
`EllipticCurves.Torsion.TwoTorsionOrder`'s `eval_ΨSq_adjacent_ne_zero_of_eval_ΨSq_eq_zero` with
`(2 : F) ≠ 0` deleted and nothing in its place.

The route is the landed one: a root `x` of `ΨSqₙ` carries a point `(x, y)` of `W`, which is then
killed by `n`, and neither neighbour of `n` can kill it as well.  **Both halves of the landed
proof's `h2` are substitutions**: `exists_equation'`
(`EllipticCurves.Torsion.ThreeTorsionStructure`) produces the point over any algebraically closed
field, its `y` coming from a degree-`2` polynomial in `Y` rather than from a square root, and
`nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic'` above is the dictionary.

⚠️ This is still the *pointwise* statement and not `IsCoprime (ΨSq_{n+1} · ΨSq_{n−1}) (ΨSq n)` over
an arbitrary commutative ring, which is `#1184` and is not reached here. -/
theorem eval_ΨSq_adjacent_ne_zero_of_eval_ΨSq_eq_zero' [IsAlgClosed F] [W.IsElliptic] {n : ℕ}
    (hn : n ≠ 0) {x : F} (hΨ : (W.ΨSq (n : ℤ)).eval x = 0) :
    (W.ΨSq ((n : ℤ) + 1)).eval x * (W.ΨSq ((n : ℤ) - 1)).eval x ≠ 0 := by
  classical
  obtain ⟨y, hxy⟩ := exists_equation' (W := W) x
  have hns : W.Nonsingular x y := equation_iff_nonsingular.mp hxy
  have hψn : (W.ψ (n : ℤ)).evalEval x y = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by rw [ψ_sq_evalEval hxy, hΨ])
  have hz : ((n : ℕ) • Point.some x y hns : W.Point) = 0 :=
    (nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic' hns n).mpr hψn
  refine mul_ne_zero ?_ ?_
  · rw [← ψ_sq_evalEval hxy]
    exact pow_ne_zero 2 (ψ_add_one_evalEval_ne_zero_of_nsmul_eq_zero' hns hz)
  · rw [← ψ_sq_evalEval hxy]
    exact pow_ne_zero 2 (ψ_sub_one_evalEval_ne_zero_of_nsmul_eq_zero' hns hn hz)

/-- **`Φₙ` and `ΨSqₙ` have no common root over an algebraically closed field, in every
characteristic** — `EllipticCurves.Torsion.TwoTorsionOrder`'s
`eval_Φ_ne_zero_of_eval_ΨSq_eq_zero` with `(2 : F) ≠ 0` deleted and nothing in its place.  This is
the `hroot` of `nsmul_surjective_of_root'`.

The step from the two neighbours to `Φₙ` is the hypothesis-free
`WeierstrassCurve.eval_Φ_ne_zero_of_eval_ΨSq_adjacent_ne_zero`
(`EllipticCurves.DivisionPolynomial.Coprime`) and is unchanged; the whole of the work is
`eval_ΨSq_adjacent_ne_zero_of_eval_ΨSq_eq_zero'` above. -/
theorem eval_Φ_ne_zero_of_eval_ΨSq_eq_zero' [IsAlgClosed F] [W.IsElliptic] {n : ℕ} (hn : n ≠ 0)
    (x : F) (hΨ : (W.ΨSq (n : ℤ)).eval x = 0) : (W.Φ (n : ℤ)).eval x ≠ 0 :=
  WeierstrassCurve.eval_Φ_ne_zero_of_eval_ΨSq_adjacent_ne_zero hΨ
    (eval_ΨSq_adjacent_ne_zero_of_eval_ΨSq_eq_zero' hn hΨ)

section Surjective

variable [DecidableEq F]

/-- ⚠️⚠️ **MULTIPLICATION BY `n` IS SURJECTIVE ON `E(F̄)` AT EVERY `n ≠ 0`, WITH NO HYPOTHESIS ON
`2` AND NO `hroot`** — over an algebraically closed field on an elliptic curve, and that is the
whole signature.

This is `EllipticCurves.Torsion.TwoTorsionOrder`'s `nsmul_surjective_of_two_ne_zero` with
`(2 : F) ≠ 0` deleted, and it is strictly stronger than
`EllipticCurves.Torsion.HasXCoordFormulaCharFree`'s `nsmul_surjective_of_root'`, whose `hroot`
`eval_Φ_ne_zero_of_eval_ΨSq_eq_zero'` above discharges over an algebraically closed field.

⚠️ **The landed name is kept and this one is additive.**  Every `EllipticCurves.TateModule`
docstring that cites `nsmul_surjective_of_two_ne_zero` by name, and every proof that uses it, is
untouched.

⚠️ **One application and no new mathematics**: the two `h2` sources of the landed statement are
`nsmul_surjective_of_root`, killed in `EllipticCurves.Torsion.HasXCoordFormulaCharFree`, and
`eval_Φ_ne_zero_of_eval_ΨSq_eq_zero`, killed above. -/
theorem nsmul_surjective [IsAlgClosed F] [W.IsElliptic] {n : ℕ} (hn : n ≠ 0) :
    Function.Surjective fun P : W.Point => n • P :=
  nsmul_surjective_of_root' hn (eval_Φ_ne_zero_of_eval_ΨSq_eq_zero' hn)

end Surjective

/-! ## ⚠️ Characteristic `2`, exhibited and not asserted -/

section CharTwo

/-- ⚠️ **The base field really is of characteristic `2`.**  `ZMod 2` has characteristic `2` and the
structure map into its algebraic closure is a ring hom between fields, hence injective. -/
private lemma two_eq_zero_algClosureZModTwo : (2 : AlgebraicClosure (ZMod 2)) = 0 := by
  have : CharP (AlgebraicClosure (ZMod 2)) 2 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2))).injective 2
  exact_mod_cast CharP.cast_eq_zero (AlgebraicClosure (ZMod 2)) 2

/-- `y² + xy = x³ + 1` over `AlgebraicClosure (ZMod 2)` — the tuple `⟨1, 0, 0, 0, 1⟩`.

⚠️ This is the same tuple over the same field as
`EllipticCurves.Torsion.ThreeTorsionStructure`'s `curveAlgClosureCharTwo`, and it is written out
again here rather than imported because that declaration and its `IsElliptic` instance are
`private` to that file.  ⚠️ `noncomputable` because `AlgebraicClosure.instField` is. -/
private noncomputable def curveAlgClosureCharTwo : Affine (AlgebraicClosure (ZMod 2)) :=
  ⟨1, 0, 0, 0, 1⟩

/-- `Δ = 1` on that curve, so the witness is not a singular equation dressed up as one:
`b₂ = 1`, `b₄ = 0`, `b₆ = 4`, `b₈ = 1`, and
`Δ = -b₂²b₈ - 8b₄³ - 27b₆² + 9b₂b₄b₆ = -1 - 432 = -433`, which is `1 - 217 · 2`.

⚠️ **No form of `decide` is available over this field**, which carries no `DecidableEq`, so the
arithmetic goes through `linear_combination` against `two_eq_zero_algClosureZModTwo`. -/
private lemma Δ_curveAlgClosureCharTwo : curveAlgClosureCharTwo.Δ = 1 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, curveAlgClosureCharTwo]
  linear_combination (-217 : AlgebraicClosure (ZMod 2)) * two_eq_zero_algClosureZModTwo

/-- The witness is a genuine elliptic curve. -/
private instance : curveAlgClosureCharTwo.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, Δ_curveAlgClosureCharTwo]
  exact isUnit_one

/-- ⚠️⚠️ **`hroot` AT EVERY INDEX ON AN ELLIPTIC CURVE OVER AN ALGEBRAICALLY CLOSED FIELD OF
CHARACTERISTIC `2`** — the statement `eval_Φ_ne_zero_of_eval_ΨSq_eq_zero` cannot be instantiated
at, since its `(2 : F) ≠ 0` is false here, and `two_eq_zero_algClosureZModTwo` above says so of
this very field.

⚠️ This certificate needs no `DecidableEq` and is therefore the sharper half of the pair below: it
is the `hroot` of `nsmul_surjective_of_root'` supplied in characteristic `2`, with no classical
instance in its statement.  ⚠️ Its proof term is another matter, and the scope of the claim is the
signature only: `eval_ΨSq_adjacent_ne_zero_of_eval_ΨSq_eq_zero'` above opens with `classical`, so
`#print axioms` on this certificate reports `Classical.choice`. -/
private theorem eval_Φ_ne_zero_of_eval_ΨSq_eq_zero_curveAlgClosureCharTwo {n : ℕ} (hn : n ≠ 0)
    (x : AlgebraicClosure (ZMod 2)) (hΨ : (curveAlgClosureCharTwo.ΨSq (n : ℤ)).eval x = 0) :
    (curveAlgClosureCharTwo.Φ (n : ℤ)).eval x ≠ 0 :=
  eval_Φ_ne_zero_of_eval_ΨSq_eq_zero' hn x hΨ

open Classical in
/-- ⚠️⚠️ **`[n]` IS SURJECTIVE ON `E(F̄)` AT EVERY `n ≠ 0` ON AN ELLIPTIC CURVE IN CHARACTERISTIC
`2`**, for `y² + xy = x³ + 1` over `AlgebraicClosure (ZMod 2)`.  This is the non-vacuity of
`nsmul_surjective` above, and the landed `nsmul_surjective_of_two_ne_zero` cannot be instantiated
here at any `n`.

⚠️ **`open Classical in` is load-bearing and is not cosmetic.**  `W.Point`'s group structure is
Mathlib's `[DecidableEq F]` one and `AlgebraicClosure (ZMod 2)` carries no such instance, so the
`n • P` of this statement is the one the classical instance builds.  ⚠️ That is a statement about
which `AddCommGroup W.Point` term is meant and not a hypothesis on the curve or on `n`;
`eval_Φ_ne_zero_of_eval_ΨSq_eq_zero_curveAlgClosureCharTwo` above is the same content with no
instance question in it at all. -/
private theorem nsmul_surjective_curveAlgClosureCharTwo {n : ℕ} (hn : n ≠ 0) :
    Function.Surjective fun P : curveAlgClosureCharTwo.Point => n • P :=
  nsmul_surjective hn

end CharTwo

end WeierstrassCurve.Affine
