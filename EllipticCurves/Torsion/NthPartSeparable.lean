/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.TriplingSeparable
import EllipticCurves.Torsion.TwoTorsionHalvingSquare

/-!
# The `n`-th-part polynomial is separable at every index, with no parity and no torsion

`Φₙ − C x₀ · ΨSqₙ` is the polynomial whose roots are the `x`-coordinates of the points `P` with
`n • P = S`, where `S` is a point of `W` above `x₀`.  Its separability is what makes the field it
generates a *separable* — hence, after a Galois closure, a Galois — extension, and `#2296`'s part
(a) item 3 names it as the one blocker left between `EllipticCurves.Torsion.NDivisionField`'s
general-`n` division field and an `n`-th part of a point.

**This file proves it at EVERY `n`, from `Ψ₂Sq(x₀) ≠ 0` alone.**  No parity hypothesis, no torsion
hypothesis on `x₀`, no `y`-coordinate, no `[DecidableEq F]` and no `[IsAlgClosed F]`.

## ⚠️⚠️ What the blocker actually was, measured rather than quoted

`EllipticCurves.Torsion.NDivisionField`'s `## What is *not* here` says the tree's only members of
this family are `separable_Φ_three_sub_C_mul_ΨSq` at `n = 3` and the `n = 2` degeneration
`Φ_two_sub_C_mul_Ψ₂Sq_eq_halvingX_sq`.  ⚠️ **That was already false when it was written.**
`EllipticCurves.Torsion.TriplingSeparable`'s `separable_Φ_sub_C_mul_ΨSq_of_odd` is the general-`n`
member and had been in the tree for seven days at that point, with the `n = 3` statement reduced to
its corollary; that bullet is corrected by this round in the one place it occurs.

So the residue was never *"no general index"*.  **It was the parity hypothesis**, and
`TriplingSeparable` priced it exactly: `Odd n` is consumed at three places, the first two
(`nsmul_eq_zero_iff_eval_preΨ_eq_zero` and `ΨSq_natCast_eq_sq_of_odd`) *binding* it and **false** at
an even index, and the third — the injectivity step — *"merely unproved"*.

## ⚠️ How all three parity debts are discharged at once

**By not incurring them.**  Each of the three exists only because the hypothesis was stated as
`preΨₙ(x₀) = 0`, i.e. as *"`x₀` is the `x`-coordinate of an `n`-torsion point"*, and the proof then
has to recover that point and reason about its order.

* ⚠️ **Debt 1, the torsion criterion** (`preΨₙ(x) = 0 ↔ n • P = 0`, used to see that a fibre point
  has `ΨSqₙ(x) ≠ 0`).  Replaced by `nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic`
  (`EllipticCurves.Torsion.TwoTorsionOrder`), which binds **no** parity, composed with
  `ψ_sq_evalEval`: if `ΨSqₙ(x) = 0` then `ψₙ(x, y) = 0`, so `n • P = 0` and `S = 0`.
* ⚠️ **Debt 2, the two-spellings bridge** `ΨSq_natCast_eq_sq_of_odd`.  **Not needed by the four
  statements**: the hypothesis is about `Ψ₂Sq` and never about `preΨₙ`, so `ΨSqₙ` is never
  re-spelled there — ⚠️ it returns only in the explicit-square `example` below.
* ⚠️⚠️ **Debt 3, the injectivity step.**  `x(P) = x(Q)` on the fibre forces `Q = ±P`, and `Q = −P`
  forces `2 • S = 0`.  At odd `n` that is contradicted via `n • S = 0`; here it contradicts the
  hypothesis **outright**, because `Ψ₂Sq(x₀) ≠ 0` *is* `2 • S ≠ 0`.

⚠️ **The hypothesis is therefore not a weakening dressed up as a strengthening**: it is the exact
condition the injectivity step needs, and the `n • S = 0` that used to supply it is gone with the
parity.  **At odd `n` it is automatic**, which is `eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero_of_odd`
below, and that is what makes `TriplingSeparable`'s four general statements corollaries — and its
four `n = 3` corollaries with them, each of those reducing to a general form in that file, one of
them (`separable_Φ_three_sub_C_mul_Ψ₃_sq`) only by way of a sibling corollary.

## ⚠️ And it is SHARP, at the one index where sharpness is decidable

`separable_Φ_two_sub_C_mul_Ψ₂Sq_iff` is an **iff** at `n = 2`: the polynomial is separable exactly
when `Ψ₂Sq(x₀) ≠ 0`.  ⚠️ **`TriplingSeparable` records that `Odd n` *"is NOT claimed to be
sharp"*; `Ψ₂Sq(x₀) ≠ 0` is, at `n = 2`.**  The converse is `isSquare_Φ_two_sub_C_mul_Ψ₂Sq_iff`
(`EllipticCurves.Torsion.TwoTorsionHalvingSquare`) plus `degree_halvingX = 2`: at a root of `Ψ₂Sq`
the polynomial is `halvingX²`, and a square of a degree-`2` polynomial is not squarefree.

## Main results

⚠️ Every public declaration of this file is listed: **4 public, 8 source-declared `private`, 4
listed**, with the listed set equal to the public set name for name.  ⚠️ **The unit there is the
source line**: the elaborated environment reads **15** private constants in this module, the extra
**7** being `fibreEquivTorsion`'s six `_proof_k` and `xCoordOf`'s `match_1`, which no source line
declares.  ⚠️ **And the five `example`s below generate no constant at all**, which is what makes
them recoveries rather than restatements.

* `WeierstrassCurve.Affine.eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero_of_odd` : at odd `n` with
  `(2 : F) ≠ 0`, a root of `preΨₙ` is never a root of `Ψ₂Sq` — *an `n`-torsion `x`-coordinate at
  odd `n` is never a `2`-torsion `x`-coordinate*.  This is what makes the odd forms corollaries.
* `WeierstrassCurve.Affine.separable_Φ_sub_C_mul_ΨSq_of_isAlgClosed_of_eval_Ψ₂Sq_ne_zero` : the
  statement over an algebraically closed field, at **every** `n`, binding `(2 : F) ≠ 0`,
  `(n : F) ≠ 0` and `Ψ₂Sq(x₀) ≠ 0`.  The content is here.
* `WeierstrassCurve.Affine.separable_Φ_sub_C_mul_ΨSq_of_eval_Ψ₂Sq_ne_zero` : **the headline**, the
  same statement over an **arbitrary** field, by base change to the algebraic closure.
* `WeierstrassCurve.Affine.separable_Φ_two_sub_C_mul_Ψ₂Sq_iff` : the sharpness **iff** at `n = 2`.

## ⚠️ What is *not* here

* **No tower, no extension field and no Galois statement.**  `#2296`'s part (a) item 3 asks for a
  finite Galois `N` over which a given `S` is `n` times another point; this file supplies the
  separability that makes such an `N` reachable and adjoins nothing.  ⚠️ **It is a prerequisite
  discharged, not the rung delivered**, and `EllipticCurves.Torsion.HalvingGaloisTower` is the
  shape the remaining work takes at `n = 2`.
* ⚠️⚠️ **Nothing at a `2`-torsion `S`, and it is FALSE there at `n = 2`.**  `Ψ₂Sq(x₀) ≠ 0` is
  exactly *"`S` is not `2`-torsion"*, and the `iff` below shows the hypothesis cannot be dropped.
  ⚠️ **So an `n`-th part of a `2`-torsion point is a genuine exception and not an oversight**, and a
  tower over such an `S` has to be built from the factorisation rather than from separability.
  **What happens at a `2`-torsion `x₀` and even `n > 2` is not decided here.**
* **No claim about irreducibility, and no factorisation.**  `Separable` is squarefreeness plus a
  derivative condition; nothing below says the polynomial is irreducible, or anything about the
  `F`-rationality of any of its `n²` roots.
* **No `y`-coordinate statement.**  A tower also needs the Weierstrass equation solved in `y` at a
  root; that quadratic is `EllipticCurves.Torsion.HalvingExtension`'s `halvingY`, which is
  index-free and already carries its discriminant there.  It is not restated.
* **Nothing landed is re-proved and nothing landed is edited** beyond one bullet of
  `EllipticCurves.Torsion.NDivisionField`'s own `## What is *not* here`, which named this family's
  members and would otherwise be stale as well as false.

## Non-vacuity

⚠️ **The hypothesis is `Ψ₂Sq(x₀) ≠ 0`, which is an OPEN condition, so non-vacuity is cheap — and
the point is WHICH instances are now available.**  On `EllipticCurves.Fixture.y2AddYEqX3` at
`R = ℚ` — `y² + y = x³`, with `b₂ = b₄ = b₈ = 0` and `b₆ = 1`, so `Ψ₂Sq = 4X³ + 1` — two
instantiations are taken and **both are at the EVEN index `n = 4`, which no landed statement of
this tree can reach**:

* at `x₀ = 0`, the `3`-torsion `x`-coordinate `TriplingSeparable`'s own fixture block uses at
  `n = 3`.  ⚠️ **The same curve and the same `x₀`, one index up and even.**
* at `x₀ = 1`, where `Ψ₂Sq(1) = 5 ≠ 0` and `Ψ₃(1) = 6 ≠ 0`.  ⚠️⚠️ **`y² + y = 1` has no rational
  root, so there is no point of the curve over `ℚ` above `x₀ = 1` at all** — which is the
  hypothesis-shape claim exhibited rather than asserted: no `y`-coordinate over `F` is asked for,
  and `x₀` need not be a torsion `x`-coordinate.

⚠️ **Certified inhabited and NOT certified informative**: `ℚ` has characteristic `0`, so `Separable`
and `Squarefree` agree there, and the characteristic-`p` case the statement exists for is not
exercised by any fixture in this tree.  That is the same limit
`EllipticCurves.Torsion.TriplingSeparable`'s own `## Non-vacuity` states.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and III.6
-/

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-! ### Two conveniences restated because they are `private` where they live

⚠️ **Both declarations below are verbatim copies of `private` declarations of
`EllipticCurves.Torsion.TriplingSeparable`**, which a different module cannot name.  They are
restated rather than made public there because publishing a total `x`-coordinate and a coset
equivalence is a decision about that module's interface and not this round's to take.  ⚠️ `#1255`
is the precedent for the opposite resolution, and `eval_Φ_three_ne_zero_of_root_ΨSq`
(`EllipticCurves.Torsion.TriplingSurjective`) records it in its own docstring. -/

/-- The `x`-coordinate of a point, with the point at infinity sent to `0`.  ⚠️ The junk value is
never read: every use below is guarded by a proof that the point is affine. -/
private def xCoordOf : W.Point → F
  | .zero => 0
  | .some x _ _ => x

private lemma xCoordOf_some {x y : F} (h : W.Nonsingular x y) :
    xCoordOf (Point.some x y h) = x := rfl

section Fibre

variable [DecidableEq F] [W.IsElliptic]

/-- **The fibre of `[n]` over a point in its image is a coset of `E[n]`**, at every `n` and over
every field.  ⚠️ Nothing about elliptic curves beyond the group law enters: the map is `P ↦ P − P₀`
in an abelian group, and `[W.IsElliptic]` is what makes `W.Point` that group. -/
private noncomputable def fibreEquivTorsion {n : ℕ} {S P₀ : W.Point} (hP₀ : n • P₀ = S) :
    {P : W.Point // n • P = S} ≃ W.torsion n where
  toFun P := ⟨P.1 - P₀, mem_torsion_iff.mpr (by rw [smul_sub, P.2, hP₀, sub_self])⟩
  invFun T := ⟨T.1 + P₀, by rw [smul_add, mem_torsion_iff.mp T.2, zero_add, hP₀]⟩
  left_inv P := Subtype.ext (sub_add_cancel _ _)
  right_inv T := Subtype.ext (add_sub_cancel_right _ _)

end Fibre

/-! ### At every index, over an algebraically closed field -/

section AlgClosed

variable [IsAlgClosed F] [W.IsElliptic]

/-- **`Φₙ − C x₀ · ΨSqₙ` is separable at EVERY `n`, over an algebraically closed field** with
`(2 : F) ≠ 0`, `(n : F) ≠ 0` and `Ψ₂Sq(x₀) ≠ 0`.

⚠️⚠️ **No parity hypothesis and no torsion hypothesis on `x₀`.**  The mathematics is
`EllipticCurves.Torsion.TriplingSeparable`'s: a bijection between the fibre `{P : n • P = S}` and
the root set, `n²` points against `n²` roots against degree `n²`, where `S` is a point above `x₀`.
What changes is the hypothesis, and with it all three of that proof's uses of `Odd n` — the module
docstring's `## ⚠️ How all three parity debts are discharged at once` walks them one by one.

⚠️ **`Ψ₂Sq(x₀) ≠ 0` enters as `2 • S ≠ 0` and is spent at exactly two places**: on `S ≠ 0`, which
is what makes every fibre point affine, and on the injectivity step, where `x(P) = x(Q)` with
`Q = −P` forces `2 • S = 0`.  ⚠️ **It is NOT spent on the count**: the fibre has `n²` elements for
every `S` in the image of `[n]`, by `fibreEquivTorsion` and `card_torsion_eq_sq`
(`EllipticCurves.Torsion.StructureGeneral`), and no hypothesis on `S` enters there. -/
theorem separable_Φ_sub_C_mul_ΨSq_of_isAlgClosed_of_eval_Ψ₂Sq_ne_zero (h2 : (2 : F) ≠ 0)
    {n : ℕ} (hn : (n : F) ≠ 0) {x₀ : F} (hx₀ : W.Ψ₂Sq.eval x₀ ≠ 0) :
    (W.Φ n - C x₀ * W.ΨSq n).Separable := by
  classical
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨y₀, hy₀⟩ := exists_equation (W := W) h2 x₀
  have hS : W.Nonsingular x₀ y₀ := equation_iff_nonsingular.mp hy₀
  set S : W.Point := Point.some x₀ y₀ hS with hSdef
  -- `Ψ₂Sq(x₀) ≠ 0` is `ψ₂(x₀, y₀) ≠ 0` is `2 • S ≠ 0`
  have hψ₂ : (W.ψ 2).evalEval x₀ y₀ ≠ 0 := fun hc =>
    hx₀ (by rw [← ΨSq_two, ← ψ_sq_evalEval hy₀, hc]; ring)
  have h2S : (2 : ℕ) • S ≠ 0 := by
    intro hc
    refine hψ₂ ?_
    have h := (nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic h2 hS 2).mp hc
    exact_mod_cast h
  have hSne : S ≠ 0 := fun hc => h2S (by rw [hc, smul_zero])
  set g : F[X] := W.Φ n - C x₀ * W.ΨSq n with hgdef
  have hdeg : g.natDegree = n ^ 2 := natDegree_Φ_sub_C_mul_ΨSq (W := W) hn0 x₀
  have hg0 : g ≠ 0 := fun h => by
    rw [h] at hdeg; exact (pow_ne_zero 2 hn0) (by simpa using hdeg.symm)
  have hsplits : g.Splits := IsAlgClosed.splits g
  have hrc : Multiset.card g.roots = n ^ 2 := by rw [splits_iff_card_roots.mp hsplits, hdeg]
  have hgeval : ∀ x : F, g.eval x = (W.Φ n).eval x - x₀ * (W.ΨSq n).eval x := by
    intro x; rw [hgdef, eval_sub, eval_mul, eval_C]
  -- a root of `g` is not a root of `ΨSqₙ`, because `Φₙ` and `ΨSqₙ` have no common root
  have hne_of_root : ∀ x : F, g.eval x = 0 → (W.ΨSq n).eval x ≠ 0 := by
    intro x hx h0
    refine eval_Φ_ne_zero_of_eval_ΨSq_eq_zero (W := W) h2 hn0 x h0 ?_
    rw [hgeval, h0, mul_zero, sub_zero] at hx
    exact hx
  -- ⚠️ debts 1 and 2 paid: a fibre point has `ΨSqₙ(x) ≠ 0` because otherwise `n • P = 0 = S`
  have hΨ_of_fibre : ∀ {x y : F} (hns : W.Nonsingular x y), (n : ℕ) • Point.some x y hns = S →
      (W.ΨSq n).eval x ≠ 0 := by
    intro x y hns hP h0
    refine hSne ?_
    rw [← hP, nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic h2 hns n]
    have hsq : (W.ψ (n : ℤ)).evalEval x y ^ 2 = 0 := by rw [ψ_sq_evalEval hns.left]; exact h0
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  -- a point of the fibre is affine and its `x`-coordinate is a root of `g`
  have hfwd : ∀ P : W.Point, n • P = S → g.eval (xCoordOf P) = 0 := by
    rintro (_ | ⟨x, y, hns⟩) hP
    · exact absurd (by rw [← hP, show (Point.zero : W.Point) = 0 from rfl, smul_zero]) hSne.symm
    · have hΨ : (W.ΨSq n).eval x ≠ 0 := hΨ_of_fibre hns hP
      obtain ⟨y', h', hxy⟩ := hasXCoordFormula_of_two_ne_zero (W := W) h2 n hns hΨ
      rw [hP, hSdef] at hxy
      have hx0 : (W.Φ n).eval x / (W.ΨSq n).eval x = x₀ :=
        (((Point.some.injEq _ _ _ _ _ _).mp hxy).1).symm
      rw [xCoordOf_some, hgeval, ← hx0, div_mul_cancel₀ _ hΨ, sub_self]
  -- ⚠️ debt 3 paid: `P = −Q` forces `2 • S = 0`, which the hypothesis contradicts outright
  have hinj : ∀ P Q : W.Point, n • P = S → n • Q = S →
      xCoordOf P = xCoordOf Q → P = Q := by
    rintro (_ | ⟨x, y, hns⟩) Q hP hQ hxx
    · exact absurd (by rw [← hP, show (Point.zero : W.Point) = 0 from rfl, smul_zero]) hSne.symm
    rcases Q with _ | ⟨x', y', hns'⟩
    · exact absurd (by rw [← hQ, show (Point.zero : W.Point) = 0 from rfl, smul_zero]) hSne.symm
    rw [xCoordOf_some, xCoordOf_some] at hxx
    rcases (Point.X_eq_iff (h₁ := hns) (h₂ := hns')).mp hxx with hc | hc
    · exact hc
    · refine absurd ?_ h2S
      have hSS : S = -S := by
        nth_rewrite 1 [← hP]
        rw [hc, smul_neg, hQ]
      rw [two_nsmul]
      nth_rewrite 1 [hSS]
      exact neg_add_cancel S
  -- every root of `g` is the `x`-coordinate of a point of the fibre
  have hsurj : ∀ x : F, g.eval x = 0 → ∃ P : W.Point, n • P = S ∧ xCoordOf P = x := by
    intro x hx
    have hΨ := hne_of_root x hx
    obtain ⟨y, hy⟩ := exists_equation (W := W) h2 x
    have hns : W.Nonsingular x y := equation_iff_nonsingular.mp hy
    obtain ⟨y', h', hxy⟩ := hasXCoordFormula_of_two_ne_zero (W := W) h2 n hns hΨ
    have hx0 : (W.Φ n).eval x / (W.ΨSq n).eval x = x₀ := by
      rw [hgeval] at hx
      rw [sub_eq_zero.mp hx, mul_div_assoc, div_self hΨ, mul_one]
    rcases (Point.X_eq_iff (h₁ := h') (h₂ := hS)).mp hx0 with hc | hc
    · exact ⟨Point.some x y hns, by rw [hxy, hc, hSdef], xCoordOf_some hns⟩
    · refine ⟨-Point.some x y hns, ?_, ?_⟩
      · rw [smul_neg, hxy, hc, hSdef, neg_neg]
      · rw [Point.neg_some]; rfl
  -- `n²` points in the fibre, `n²` distinct roots, degree `n²`
  obtain ⟨P₀, hP₀⟩ := nsmul_surjective_of_two_ne_zero (W := W) h2 hn0 S
  have hfib : Nat.card {P : W.Point // n • P = S} = n ^ 2 := by
    rw [Nat.card_congr (fibreEquivTorsion hP₀), card_torsion_eq_sq h2 hn]
  have hbij : Function.Bijective
      (fun P : {P : W.Point // n • P = S} => (⟨xCoordOf P.1, hfwd P.1 P.2⟩ :
        {x : F // g.eval x = 0})) := by
    constructor
    · rintro ⟨P, hP⟩ ⟨Q, hQ⟩ hPQ
      exact Subtype.ext (hinj P Q hP hQ (congrArg Subtype.val hPQ))
    · rintro ⟨x, hx⟩
      obtain ⟨P, hP, hxP⟩ := hsurj x hx
      exact ⟨⟨P, hP⟩, Subtype.ext hxP⟩
  have hrootsn : g.roots.toFinset.card = n ^ 2 := by
    rw [← card_root_subtype hg0, ← Nat.card_congr (Equiv.ofBijective _ hbij), hfib]
  exact (nodup_roots_iff_of_splits hg0 hsplits).mp
    (Multiset.toFinset_card_eq_card_iff_nodup.mp (by rw [hrootsn, hrc]))

end AlgClosed

/-! ### The descent to an arbitrary field, and the odd forms as corollaries -/

section General

variable [W.IsElliptic]

/-- **`Φₙ − C x₀ · ΨSqₙ` is separable at EVERY `n`, over an ARBITRARY field** with `(2 : F) ≠ 0`,
`(n : F) ≠ 0` and `Ψ₂Sq(x₀) ≠ 0` — the headline.

⚠️ **Neither `[DecidableEq F]` nor `[IsAlgClosed F]` nor a `y`-coordinate is bound, and `x₀` is not
asked to be a torsion `x`-coordinate.**  The hypothesis is one polynomial evaluation at one
element; `Polynomial.separable_map` moves the conclusion across `F → AlgebraicClosure F` in both
directions, `WeierstrassCurve.map_Φ` and `map_ΨSq` move the two objects, and `ΨSq_two` is what
carries `Ψ₂Sq` across as `ΨSq 2`.  The point above `x₀` exists over the closure and nowhere is it
asked to exist over `F`. -/
theorem separable_Φ_sub_C_mul_ΨSq_of_eval_Ψ₂Sq_ne_zero (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : (n : F) ≠ 0) {x₀ : F} (hx₀ : W.Ψ₂Sq.eval x₀ ≠ 0) :
    (W.Φ n - C x₀ * W.ΨSq n).Separable := by
  classical
  set K := AlgebraicClosure F with hK
  have h2' : (2 : K) ≠ 0 := fun hzero =>
    h2 ((algebraMap F K).injective (by rw [map_ofNat, map_zero]; exact hzero))
  have hn' : ((n : ℕ) : K) ≠ 0 := fun hzero =>
    hn ((algebraMap F K).injective (by rw [map_natCast, map_zero]; exact hzero))
  have hmapΨ₂ : (W⁄K).Ψ₂Sq = W.Ψ₂Sq.map (algebraMap F K) := by
    rw [← ΨSq_two, ← ΨSq_two, show (W⁄K).ΨSq (2 : ℤ) = (W.ΨSq (2 : ℤ)).map (algebraMap F K) from
      WeierstrassCurve.map_ΨSq ..]
  have hx₀' : (W⁄K).Ψ₂Sq.eval (algebraMap F K x₀) ≠ 0 := by
    rw [hmapΨ₂, eval_map, eval₂_at_apply]
    exact fun hc => hx₀ ((algebraMap F K).injective (by rw [map_zero]; exact hc))
  rw [← Polynomial.separable_map (algebraMap F K),
    show (W.Φ n - C x₀ * W.ΨSq n).map (algebraMap F K)
      = (W⁄K).Φ n - C (algebraMap F K x₀) * (W⁄K).ΨSq n by
      rw [show (W⁄K).Φ (n : ℤ) = (W.Φ (n : ℤ)).map (algebraMap F K) from WeierstrassCurve.map_Φ ..,
        show (W⁄K).ΨSq (n : ℤ) = (W.ΨSq (n : ℤ)).map (algebraMap F K) from
          WeierstrassCurve.map_ΨSq .., Polynomial.map_sub, Polynomial.map_mul, map_C]]
  exact separable_Φ_sub_C_mul_ΨSq_of_isAlgClosed_of_eval_Ψ₂Sq_ne_zero h2' hn' hx₀'

/-- **At odd `n`, an `n`-torsion `x`-coordinate is never a `2`-torsion `x`-coordinate** — a root of
`preΨₙ` is not a root of `Ψ₂Sq`, over an arbitrary field with `(2 : F) ≠ 0`.

⚠️ **This is what makes all four of `EllipticCurves.Torsion.TriplingSeparable`'s GENERAL
statements corollaries of the headline above** — and the four `n = 3` corollaries that file pairs
them with follow in turn, each reducing there to a general form, one of them
(`separable_Φ_three_sub_C_mul_Ψ₃_sq`) only by way of a sibling corollary — so the parity
hypothesis is traded for an open condition and nothing is given up.  The argument is the one
`Odd n` used to carry inside that file: over the
closure, a root of `preΨₙ` carries a point `S ≠ 0` with `n • S = 0`, a root of `Ψ₂Sq` would give
`2 • S = 0`, and writing `n = 2k + 1` then gives `S = n • S − k • (2 • S) = 0`.

⚠️ **It is stated over an arbitrary field although it is proved over the closure**: both sides are
polynomial conditions on one element, so `WeierstrassCurve.map_preΨ` and `map_ΨSq` carry them up
and the injectivity of `algebraMap` carries the conclusion back. -/
theorem eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero_of_odd (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n)
    {x₀ : F} (hx₀ : (W.preΨ (n : ℤ)).eval x₀ = 0) : W.Ψ₂Sq.eval x₀ ≠ 0 := by
  classical
  intro h0
  set K := AlgebraicClosure F with hK
  have h2' : (2 : K) ≠ 0 := fun hzero =>
    h2 ((algebraMap F K).injective (by rw [map_ofNat, map_zero]; exact hzero))
  have hx₀' : ((W⁄K).preΨ (n : ℤ)).eval (algebraMap F K x₀) = 0 := by
    rw [show (W⁄K).preΨ (n : ℤ) = (W.preΨ (n : ℤ)).map (algebraMap F K) from
      WeierstrassCurve.map_preΨ .., eval_map, eval₂_at_apply, hx₀, map_zero]
  have h0' : (W⁄K).Ψ₂Sq.eval (algebraMap F K x₀) = 0 := by
    rw [← ΨSq_two, show (W⁄K).ΨSq (2 : ℤ) = (W.ΨSq (2 : ℤ)).map (algebraMap F K) from
      WeierstrassCurve.map_ΨSq .., eval_map, eval₂_at_apply, ΨSq_two, h0, map_zero]
  obtain ⟨y₀, hy₀⟩ := exists_equation (W := W⁄K) h2' (algebraMap F K x₀)
  have hS : (W⁄K).Nonsingular (algebraMap F K x₀) y₀ := equation_iff_nonsingular.mp hy₀
  have hSn : (n • Point.some _ y₀ hS : (W⁄K).Point) = 0 :=
    (nsmul_eq_zero_iff_eval_preΨ_eq_zero h2' hodd hS).mpr hx₀'
  have hψ₂ : ((W⁄K).ψ 2).evalEval (algebraMap F K x₀) y₀ = 0 := by
    have hsq : ((W⁄K).ψ (2 : ℤ)).evalEval (algebraMap F K x₀) y₀ ^ 2 = 0 := by
      rw [ψ_sq_evalEval hy₀, ΨSq_two]; exact h0'
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  have h2S : ((2 : ℕ) • Point.some _ y₀ hS : (W⁄K).Point) = 0 := by
    rw [nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic h2' hS 2]
    exact_mod_cast hψ₂
  obtain ⟨k, hk⟩ := hodd
  have hsplit : (n • Point.some _ y₀ hS : (W⁄K).Point)
      = k • ((2 : ℕ) • Point.some _ y₀ hS : (W⁄K).Point) + Point.some _ y₀ hS := by
    rw [hk, add_nsmul, one_nsmul, mul_nsmul]
  rw [h2S, nsmul_zero, zero_add] at hsplit
  exact Point.some_ne_zero hS (hsplit.symm.trans hSn)

/-- **At `n = 2` the hypothesis is SHARP**: `Φ₂ − C x₀ · Ψ₂Sq` is separable **exactly** when
`Ψ₂Sq(x₀) ≠ 0`.

⚠️ **`EllipticCurves.Torsion.TriplingSeparable` records that its `Odd n` *"is NOT claimed to be
sharp"*.  This says `Ψ₂Sq(x₀) ≠ 0` is, at the one index where the question is decidable.**  The
reverse direction is the headline at `n = 2`; the forward one is
`isSquare_Φ_two_sub_C_mul_Ψ₂Sq_iff` (`EllipticCurves.Torsion.TwoTorsionHalvingSquare`) read
through `Separable.squarefree`: at a root of `Ψ₂Sq` the polynomial is `halvingX²`, and
`degree_halvingX = 2` says that square root is not a unit. -/
theorem separable_Φ_two_sub_C_mul_Ψ₂Sq_iff (h2 : (2 : F) ≠ 0) (x₀ : F) :
    (W.Φ 2 - C x₀ * W.Ψ₂Sq).Separable ↔ W.Ψ₂Sq.eval x₀ ≠ 0 := by
  refine ⟨fun hsep hx₀ => ?_, fun hx₀ => ?_⟩
  · rw [Φ_two_sub_C_mul_Ψ₂Sq_eq_halvingX_sq h2 hx₀] at hsep
    have hu : IsUnit (W.halvingX x₀) := hsep.squarefree _ (by rw [← sq])
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_halvingX] at hu
    exact absurd hu (by decide)
  · have h := separable_Φ_sub_C_mul_ΨSq_of_eval_Ψ₂Sq_ne_zero (W := W) h2 (n := 2)
      (by exact_mod_cast h2) hx₀
    rwa [show ((2 : ℕ) : ℤ) = (2 : ℤ) from rfl, ΨSq_two] at h

end General

/-! ### ⚠️ The landed odd-index statements, recovered

`EllipticCurves.Torsion.TriplingSeparable` has **eight** public theorems, which its own
`## Main results` describes as *"four general statements and their four `n = 3` corollaries,
paired"*.  ⚠️ **All FOUR of the general ones are recovered below from the headline and
`eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero_of_odd`, with no parity step in the separability argument**
— and that settles the other four with them, because each `n = 3` corollary reduces **in that
file** to a general form, one of them (`separable_Φ_three_sub_C_mul_Ψ₃_sq`) only through
`separable_Φ_three_sub_C_mul_ΨSq`, so nothing of the eight needs `Odd n` for a reason this round
has not discharged.  ⚠️⚠️ **Two of the four do spend `Odd n` once more, and neither spending is a
separability step**: `example` 3 spends it on the two-spellings bridge `ΨSq_natCast_eq_sq_of_odd`
and `example` 4 on the torsion criterion `nsmul_eq_zero_iff_eval_preΨ_eq_zero` — exactly the two
sites `## ⚠️⚠️ What the blocker actually was` calls *binding* and **false** at an even index.
⚠️ **A fifth `example` is taken anyway**, at `separable_Φ_three_sub_C_mul_ΨSq`, because the `Ψ₃`
spelling is the one every consumer of that file states and reading it off the general form is the
check a consumer actually wants.

⚠️ **They are anonymous `example`s and not declarations**: all eight landed names stay where they
are and none is re-stated, re-proved or deprecated. -/

section Recovery

variable [W.IsElliptic]

/-- `separable_Φ_sub_C_mul_ΨSq_of_odd` recovered. -/
example (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n) (hn : (n : F) ≠ 0) {x₀ : F}
    (hx₀ : (W.preΨ (n : ℤ)).eval x₀ = 0) : (W.Φ n - C x₀ * W.ΨSq n).Separable :=
  separable_Φ_sub_C_mul_ΨSq_of_eval_Ψ₂Sq_ne_zero h2 hn
    (eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero_of_odd h2 hodd hx₀)

/-- `separable_Φ_sub_C_mul_ΨSq_of_isAlgClosed_of_odd` recovered. -/
example [IsAlgClosed F] (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n) (hn : (n : F) ≠ 0) {x₀ : F}
    (hx₀ : (W.preΨ (n : ℤ)).eval x₀ = 0) : (W.Φ n - C x₀ * W.ΨSq n).Separable :=
  separable_Φ_sub_C_mul_ΨSq_of_isAlgClosed_of_eval_Ψ₂Sq_ne_zero h2 hn
    (eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero_of_odd h2 hodd hx₀)

/-- `separable_Φ_sub_C_mul_preΨ_sq_of_odd` recovered, in the explicit-square spelling. -/
example (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n) (hn : (n : F) ≠ 0) {x₀ : F}
    (hx₀ : (W.preΨ (n : ℤ)).eval x₀ = 0) :
    (W.Φ n - C x₀ * W.preΨ (n : ℤ) ^ 2).Separable := by
  have h := separable_Φ_sub_C_mul_ΨSq_of_eval_Ψ₂Sq_ne_zero (W := W) h2 hn
    (eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero_of_odd h2 hodd hx₀)
  rwa [ΨSq_natCast_eq_sq_of_odd (W := W) hodd] at h

/-- `separable_Φ_sub_C_mul_ΨSq_of_mem_torsion_of_odd` recovered.  ⚠️ **This is the only one of the
four that binds `[DecidableEq F]`**, and it binds it because `W.torsion` does; nothing in the route
below needs it. -/
example [DecidableEq F] (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n) (hn : (n : F) ≠ 0) {x₀ y₀ : F}
    (hS : W.Nonsingular x₀ y₀) (hSn : Point.some x₀ y₀ hS ∈ W.torsion n) :
    (W.Φ n - C x₀ * W.ΨSq n).Separable :=
  separable_Φ_sub_C_mul_ΨSq_of_eval_Ψ₂Sq_ne_zero h2 hn
    (eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero_of_odd h2 hodd
      ((nsmul_eq_zero_iff_eval_preΨ_eq_zero h2 hodd hS).mp (mem_torsion_iff.mp hSn)))

/-- `separable_Φ_three_sub_C_mul_ΨSq` recovered, in the `Ψ₃` spelling every consumer uses. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x₀ : F} (hx₀ : W.Ψ₃.eval x₀ = 0) :
    (W.Φ 3 - C x₀ * W.ΨSq 3).Separable := by
  have hpre : (W.preΨ ((3 : ℕ) : ℤ)).eval x₀ = 0 := by
    rw [show ((3 : ℕ) : ℤ) = (3 : ℤ) by norm_num, preΨ_three]; exact hx₀
  simpa using separable_Φ_sub_C_mul_ΨSq_of_eval_Ψ₂Sq_ne_zero (W := W) h2 (n := 3)
    (by exact_mod_cast h3) (eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero_of_odd h2 (by decide) hpre)

end Recovery

/-! ### ⚠️ Non-vacuity, at an EVEN index

⚠️ **Both instantiations below are at `n = 4`, and no landed statement of this tree reaches an even
index at all.**  The curve is `EllipticCurves.Fixture.y2AddYEqX3` at `R = ℚ`; the module
docstring's `## Non-vacuity` says why these two `x₀` and what each exhibits. -/

section Nonvacuity

open EllipticCurves.Fixture

/-- **`Ψ₂Sq = 4X³ + 1` on `y² + y = x³`**, from `b₂ = b₄ = 0` and `b₆ = 1`. -/
private lemma Ψ₂Sq_y2AddYEqX3 : (y2AddYEqX3 ℚ).Ψ₂Sq = C 4 * X ^ 3 + 1 := by
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, y2AddYEqX3]
  norm_num

/-- `Ψ₂Sq(0) = 1 ≠ 0`, so the `3`-torsion `x`-coordinate `0` is not a `2`-torsion one. -/
private lemma eval_Ψ₂Sq_zero_ne_y2AddYEqX3 : (y2AddYEqX3 ℚ).Ψ₂Sq.eval 0 ≠ 0 := by
  rw [Ψ₂Sq_y2AddYEqX3]; norm_num

/-- `Ψ₂Sq(1) = 5 ≠ 0`, and ⚠️ `y² + y = 1` has no rational root, so there is no point of this
curve over `ℚ` above `x₀ = 1`. -/
private lemma eval_Ψ₂Sq_one_ne_y2AddYEqX3 : (y2AddYEqX3 ℚ).Ψ₂Sq.eval 1 ≠ 0 := by
  rw [Ψ₂Sq_y2AddYEqX3]; norm_num

/-- **The `4`-th-part polynomial of `x₀ = 0` on `y² + y = x³` over `ℚ` is separable** — the headline
inhabited at an **even** index, at the very `x₀` that `TriplingSeparable`'s fixture block uses at
`n = 3`.  ⚠️ **No statement of this tree before this round could state it.** -/
private theorem exampleSeparableFourthPart :
    ((y2AddYEqX3 ℚ).Φ 4 - C (0 : ℚ) * (y2AddYEqX3 ℚ).ΨSq 4).Separable :=
  separable_Φ_sub_C_mul_ΨSq_of_eval_Ψ₂Sq_ne_zero (by norm_num) (n := 4) (by norm_num)
    eval_Ψ₂Sq_zero_ne_y2AddYEqX3

/-- **The same at `x₀ = 1`, which is not a torsion `x`-coordinate and carries no `ℚ`-point at
all** — ⚠️ the two hypotheses this round drops, exhibited rather than asserted. -/
private theorem exampleSeparableFourthPartNonTorsion :
    ((y2AddYEqX3 ℚ).Φ 4 - C (1 : ℚ) * (y2AddYEqX3 ℚ).ΨSq 4).Separable :=
  separable_Φ_sub_C_mul_ΨSq_of_eval_Ψ₂Sq_ne_zero (by norm_num) (n := 4) (by norm_num)
    eval_Ψ₂Sq_one_ne_y2AddYEqX3

end Nonvacuity

end WeierstrassCurve.Affine
