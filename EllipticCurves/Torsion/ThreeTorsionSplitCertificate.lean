/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.ThreeTorsionStructure
import Mathlib.FieldTheory.Finite.Basic

/-!
# A non-vacuity certificate for the `n = 3` structure theorem

`EllipticCurves.Torsion.ThreeTorsionStructure` proves `#E[3] = 9` and `E[3] ≃+ ZMod 3 × ZMod 3`
for an elliptic curve over a field of characteristic `≠ 2, 3` satisfying

```
hsplits : W.Ψ₃.Splits          hsq : ∀ x, W.Ψ₃.eval x = 0 → IsSquare (W.Ψ₂Sq.eval x)
```

and ships **no certificate that those two hypotheses are jointly satisfiable** over a field that is
not algebraically closed.  This file is that certificate, on `y² = x³ + 2` over `ZMod 7`.

## ⚠️ Why the base is `ZMod 7` and not `ℚ`

Every other non-vacuity block in this development that discharges a splitting hypothesis does it
over `ℚ` — `EllipticCurves.Torsion.TwoTorsion` certifies `card_torsion_two_of_splits` on
`y² = x(x + 1)(x + 4)` with no extension at all — so a finite base needs a reason, and there is
one.  ⚠️ **No curve over `ℚ` can serve, and the obstruction is a theorem rather than a gap in the
search.**  The two hypotheses together say `E[3] ⊆ E(F)`; the Weil pairing `e₃ : E[3] × E[3] → μ₃`
is surjective and Galois-equivariant, so `E[3]` rational forces `μ₃ ⊆ F`.  Since `μ₃ ⊄ ℚ`, the two
hypotheses are **jointly unsatisfiable for every elliptic curve over `ℚ`**, and a `ℚ` block here
would be proving `False → _`.  The contrast with `n = 2` is exact and is the reason that file needs
no extension: `μ₂ = {±1}` is rational everywhere.

⚠️ **That argument is classical and is not formalised anywhere in this tree, and nothing in this
file rests on it.**  The Weil pairing at general `n` is `#244`'s front and its surjectivity over a
general base is not a merged statement here.  It is recorded because a reader who meets a
finite-field certificate in a tree of `ℚ` and `AlgebraicClosure ℚ` fixtures will otherwise take the
base for an arbitrary choice — this is the only one outside `FunctionField/`, and
`EllipticCurves.Fixtures` lists all of them in full.  `7 ≡ 1 mod 3`, so `μ₃ ⊆ 𝔽₇` and the base is
consistent with the obstruction, as it has to be.

## The curve, and why substituting another one is not free

`y² = x³ + 2`, i.e. `⟨0, 0, 0, 0, 2⟩ : Affine (ZMod 7)`, with

```
b₂, b₄, b₆, b₈  =  0, 0, 1, 0          Δ = -1728 = 1 ≠ 0
Ψ₃   = 3X⁴ + 3X = 3·X·(X + 1)·(X + 2)·(X + 4)      roots {0, 6, 5, 3}, four and distinct
Ψ₂Sq = 4X³ + 1                                     values {1, 4, 4, 4} there, all squares
```

⚠️ **Of the 42 pairs `(A, B)` mod `7` with `Δ ≠ 0`, this is the only one satisfying both
conditions** (exhaustive search).  So the choice is forced up to the short-Weierstrass shape, and a
substitution would very likely leave this file green and vacuous rather than merely different.

## ⚠️ `decide` does not reach the hypotheses, and that is why they are proved structurally

`Polynomial` is a `Finsupp`, which does not reduce, so

```
example : ∀ x : ZMod 7, W.Ψ₃.eval x = 0 → IsSquare (W.Ψ₂Sq.eval x) := by decide
```

fails at the `Decidable` instance.  (The `decide +kernel` used by the `IsElliptic` instance below
and by the four earlier certificates in `FunctionField/` works because `IsElliptic` is a statement
about a ring *element* — `Δ` a unit — and not about a polynomial.)  Both hypotheses are therefore
produced from polynomial identities first: `Ψ₃_exampleCurveSeven` factors `Ψ₃` into linear factors
and feeds them to `Splits.C`/`Splits.X`/`Splits.X_add_C` exactly as
`splits_Ψ₂Sq_y2EqX3Add5X2Add4X` does at `n = 2`, and `Ψ₂Sq_eval_exampleCurveSeven` turns the second
hypothesis into arithmetic in `ZMod 7`, at which point `decide` does reach it.

## Main statements

Both are `private`: nothing outside this file consumes a certificate, and the statements they
instantiate live in `ThreeTorsionStructure`.

* `card_torsion_three_exampleCurveSeven`: `#E[3] = 9` for `y² = x³ + 2` over `ZMod 7`, **with no
  hypothesis whatsoever**.
* `nonempty_torsionThree_addEquiv_exampleCurveSeven`: `E[3] ≃+ ZMod 3 × ZMod 3` for the same curve,
  likewise unconditional.

## What is *not* here

* **No field construction.**  This file exhibits a base satisfying the two conditions; it does not
  construct one from a curve, and the `3`-division field remains what
  `ThreeTorsionStructure`'s `## What is *not* here` says it is.
* **No Lean proof of the `μ₃ ⊆ F` obstruction.**  See the ⚠️ above.
* **No change to any statement of `ThreeTorsionStructure`**, whose two `_of_splits` forms are used
  here exactly as they are stated.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6, Corollary 6.4 and III.8
  (the Weil pairing and the rationality obstruction quoted above).
-/

open Polynomial

namespace WeierstrassCurve.Affine

section Nonvacuity

/-- ⚠️ Kept **local**: this file has no business adding a global `Fact (Nat.Prime 7)` instance to
the tree, and nothing outside this section needs it.  This is the shape
`EllipticCurves.FunctionField.MulByNDegreeTower` uses for its `ZMod 5` certificate. -/
private lemma fact_prime_seven : Fact (Nat.Prime 7) := ⟨by decide⟩

attribute [local instance] fact_prime_seven

/-- The curve `y² = x³ + 2` over `ZMod 7`, of discriminant `-1728 = 1`. -/
private def exampleCurveSeven : Affine (ZMod 7) := ⟨0, 0, 0, 0, 2⟩

private instance : exampleCurveSeven.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  decide +kernel

/-- The `3`-division polynomial of the example curve, factored:
`3X⁴ + 3X = 3·X·(X + 1)·(X + 2)·(X + 4)`, with the four distinct roots `0`, `6`, `5`, `3`. -/
private lemma Ψ₃_exampleCurveSeven :
    exampleCurveSeven.Ψ₃ = C 3 * X * (X + C 1) * (X + C 2) * (X + C 4) := by
  have h7 : (7 : (ZMod 7)[X]) = 0 := by
    rw [← map_ofNat (C : ZMod 7 →+* (ZMod 7)[X]) 7, show (7 : ZMod 7) = 0 by decide, map_zero]
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, exampleCurveSeven]
  norm_num only
  simp only [map_ofNat, map_one, map_zero]
  linear_combination (-3 * X ^ 3 - 6 * X ^ 2) * h7

/-- **The splitting hypothesis, discharged over `ZMod 7`** — a product of one constant and three
monic linear factors is a `Splits` witness on the nose. -/
private lemma splits_Ψ₃_exampleCurveSeven : exampleCurveSeven.Ψ₃.Splits := by
  rw [Ψ₃_exampleCurveSeven]
  exact (((Splits.C 3).mul Splits.X).mul (Splits.X_add_C 1)).mul (Splits.X_add_C 2) |>.mul
    (Splits.X_add_C 4)

/-- The `2`-division polynomial of the example curve evaluates to `4x³ + 1`. -/
private lemma Ψ₂Sq_eval_exampleCurveSeven (x : ZMod 7) :
    exampleCurveSeven.Ψ₂Sq.eval x = 4 * x ^ 3 + 1 := by
  rw [Ψ₂Sq_eval]
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, exampleCurveSeven]
  ring_nf
  decide +revert

/-- The `3`-division polynomial of the example curve evaluates to `3x⁴ + 3x`. -/
private lemma Ψ₃_eval_exampleCurveSeven (x : ZMod 7) :
    exampleCurveSeven.Ψ₃.eval x = 3 * x ^ 4 + 3 * x := by
  rw [Ψ₃_exampleCurveSeven]
  simp only [eval_mul, eval_add, eval_C, eval_X]
  ring_nf
  decide +revert

/-- **The squareness hypothesis, discharged over `ZMod 7`.**  ⚠️ The case split is on the *value*
`4x³ + 1` and not on the polynomial: at the four roots of `Ψ₃` it is `1` or `4`, and both are
squares in `ZMod 7`. -/
private lemma isSquare_Ψ₂Sq_eval_exampleCurveSeven (x : ZMod 7)
    (hx : exampleCurveSeven.Ψ₃.eval x = 0) :
    IsSquare (exampleCurveSeven.Ψ₂Sq.eval x) := by
  rw [Ψ₃_eval_exampleCurveSeven] at hx
  rw [Ψ₂Sq_eval_exampleCurveSeven]
  have h : ∀ z : ZMod 7, 3 * z ^ 4 + 3 * z = 0 → 4 * z ^ 3 + 1 = 1 ∨ 4 * z ^ 3 + 1 = 4 := by
    decide
  rcases h x hx with h1 | h4
  · rw [h1]; exact ⟨1, by decide⟩
  · rw [h4]; exact ⟨2, by decide⟩

/-- **`#E[3] = 9` over `ZMod 7`, with no hypothesis whatsoever**, for `y² = x³ + 2`. -/
private theorem card_torsion_three_exampleCurveSeven :
    Nat.card (exampleCurveSeven.torsion 3) = 9 :=
  card_torsion_three_of_splits (by decide) (by decide) splits_Ψ₃_exampleCurveSeven
    isSquare_Ψ₂Sq_eval_exampleCurveSeven

/-- **`E[3] ≃+ ZMod 3 × ZMod 3` over `ZMod 7`, with no hypothesis whatsoever**, for `y² = x³ + 2`.
This is the `n = 3` structure theorem on a curve over a field that is not algebraically closed. -/
private theorem nonempty_torsionThree_addEquiv_exampleCurveSeven :
    Nonempty (exampleCurveSeven.torsion 3 ≃+ ZMod 3 × ZMod 3) :=
  nonempty_torsionThree_addEquiv_of_splits (by decide) (by decide) splits_Ψ₃_exampleCurveSeven
    isSquare_Ψ₂Sq_eval_exampleCurveSeven

end Nonvacuity

end WeierstrassCurve.Affine
