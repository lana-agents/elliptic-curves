/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.OmegaOnCurve

/-!
# The `3`-division `y`-coordinate and the tripling map is on the curve

Mathlib's `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` develops the
`x`-coordinate division polynomials (`ψ₂, Ψ₂Sq, Ψ₃, preΨ₄, ΨSq, Ψ, Φ, ψ, φ`) but explicitly leaves
the *`y`-coordinate* division polynomials `ωₙ` as a `TODO`. Consequently there is, on the current
pin, no statement that the multiplication-by-`n` point `[n]P = (Φₙ/ΨSqₙ, ωₙ/ψₙ³)` actually lies on
the curve — the *on-curve identity* that the function-field pullback `[n]∗ : F(W) → F(W)` consumes.

The sibling file `EllipticCurves/Torsion/OmegaTwo.lean` supplies the crux for the **duplication
map** `n = 2`. This file supplies the analogue for the **tripling map** `n = 3` (Silverman AEC,
Exercise 3.7).

Both are instances of one general-`n` statement: `EllipticCurves.Torsion.OmegaOnCurve` writes the
`ψ₃`-denominator clearing and the passage from `(2Y + a₁X + a₃)² = 4X³ + b₂X² + 2b₄X + b₆` to the
Weierstrass equation once, at a general index, taking as its only index-dependent input the single
univariate identity `WeierstrassCurve.HasPreΩSqAt` — the analogue of `preΨ₄_sq`, closed by `ring`
after substituting the `bᵢ`-relation `4b₈ = b₂b₆ − b₄²`. At `n = 3` that input is
`WeierstrassCurve.Affine.hasPreΩSqAt_three`, and the theorem below is
`WeierstrassCurve.Affine.equation_of_hasPreΩSqAt` applied to it with the `n = 3` names unfolded.

Concretely: over a field of characteristic `≠ 2`, for a point `(x, y)` on `W` with `ψ₃(x, y) ≠ 0`
(i.e. `P` is not `3`-torsion), the point `(Φ₃(x)/Ψ₃(x)², ω₃(x,y)/ψ₃(x,y)³)` lies on `W`, where
`ω₃(x,y) = ((2y + a₁x + a₃)·(preΨ₅(x) − preΨ₄(x)²) − a₁·Φ₃(x)·ψ₃(x,y) − a₃·ψ₃(x,y)³) / 2`
is the value of the `3`-division `y`-coordinate polynomial.

⚠️ **That `/2` is PRESENTATIONAL, the `(2 : F) ≠ 0` beside it is NOT, and the two are independent.**
The `n = 3` bracket being halved is divisible by `2` in `ℤ[a₁,…,a₆][X][Y]` **identically** — no use
of the Weierstrass relation, no reduction of `Y²`, no localisation — so this `y`-coordinate is
an honest polynomial `ω₃ = preΩ₃·Y + preω₃` over **every** commutative ring
(`WeierstrassCurve.ω₃`, `EllipticCurves.Torsion.OmegaDivisionPolynomial`), and
`tripling_equation_ω₃` below is the on-curve identity written as `ω₃(x, y)/ψ₃(x, y)³`, with no
`2` in it anywhere.

## The two rôles of `(2 : F) ≠ 0` on this route, and its FOUR consumption sites

⚠️ **Removing the `2` from the statement does not remove the hypothesis — but it is NOT the case
that only one of its uses was ever about that `2`.**  On the route from `W.Equation x y` to
`tripling_equation_ω₃`, `h2` is consumed at **four** sites playing **two** rôles, and ⚠️ **two of
the four sites are the `2` itself.**  They are listed below in route order.

* **`hasPreΩSqAt_three`'s `hb8` step — the `b`-relation.**  ⚠️ **A binder whose own proof consumes
  what it binds is a consumption site**, and this one is readable off the script with no
  `field_simp` subtlety in it: in `EllipticCurves.Torsion.OmegaOnCurve` the line below the binder
  builds `h4 : (4 : F) ≠ 0` by `mul_ne_zero h2 h2`, and the next one spends it on
  `rw [eq_div_iff h4]` inside `hb8 : W.b₈ = (W.b₂ * W.b₆ - W.b₄ ^ 2) / 4` — which is the
  `b`-relation `4b₈ = b₂b₆ − b₄²` divided by `4`.  ⚠️ **This binder is nevertheless redundant**,
  for a reason that is about import order rather than about characteristic; see below.
* ⚠️ **`equation_of_hasPreΩSqAt`'s `hlin` step — the `2`.**  `hlin` reads
  `2·Y' + a₁X' + a₃ = e·Ov/s³` with `Y' = (e·Ov − s·(a₁Φv + a₃Ψv))/(2·s³)`, and its `field_simp`
  needs `2 ≠ 0` to clear that denominator.  ⚠️ **Measured both ways**: with `h2` in context the step
  closes, and with `h2` removed and nothing else changed `field_simp` stops at
  `e·Ov·2⁻¹·2 + … = e·Ov` and `ring` fails.  ⚠️ **And `hlin` is FALSE in characteristic `2` for a
  reason the `b`-relation plays no part in**: there `2·s³ = 0`, so its left-hand side collapses to
  `a₁X' + a₃` identically, whatever the numerator is, while its right-hand side stays `e·Ov/s³` —
  `0` against `1` at `a₁ = a₃ = Φv = 0`, `e = Ov = s = Ψv = 1` over `ZMod 2`.
* **`equation_of_hasPreΩSqAt`'s closing step — the `b`-relation.**  `mul_left_cancel₀ h4` on
  `4·(Weierstrass equation)`: the engine reaches the `ψ₂`-form
  `(2y + a₁x + a₃)² = 4x³ + b₂x² + 2b₄x + b₆` and divides by `4` to land on `Equation`.  In
  characteristic `2` that identity reads `0 = 0` and carries nothing, so **this** rôle belongs to
  the `b`-relation route and no normalisation of `ωₙ` touches it.  ⚠️ **Its `h4` is a different
  term in a different lemma from the first site's** — two byte-identical `have` lines forty lines
  apart in `OmegaOnCurve`, which is exactly what makes these two `b`-relation sites look like one.
* ⚠️ **`tripling_equation_ω₃`'s own `hy` step — the `2` again.**  It turns `…/(2·ψ₃³)` into
  `ω₃/ψ₃³` by `div_eq_div_iff (mul_ne_zero h2 h3) h3`, so ⚠️ **the theorem below pays for a `2`
  that its own conclusion does not contain.**  That is an artefact of routing through
  `tripling_equation`, whose statement still carries the `2` — not a fact about `ω₃`.

**And the first of those four sites binds a hypothesis it does not need.**
⚠️ **`hasPreΩSqAt_three`'s `h2` is redundant outright.**  Its conclusion `W.HasPreΩSqAt 3 x` binds
no characteristic hypothesis, and `WeierstrassCurve.hasPreΩSq`
(`EllipticCurves.Torsion.OmegaCrux`) proves that polynomial identity at **every** index over
**every** `CommRing`: `(W.hasPreΩSq 3).at x` is a complete `h2`-free proof of it.  ⚠️ What blocks
the removal is **import order, not mathematics** — `OmegaCrux` reaches `OmegaOnCurve`, so the
hypothesis cannot be dropped where that lemma lives, and importing `OmegaCrux` *here* to drop it
moves this file's project import closure from **3** modules to **22** (measured at this commit),
for a hypothesis the theorems below bind anyway.  **Named and priced, not paid.**  ⚠️ **Redundant
is not unconsumed**: the proof as written spends it, which is why the site above counts.

⚠️ **What the four sites add up to is stronger than *"the hypothesis survives"*.**  Both of the
`2`-rôle sites are artefacts of the **route** and not of the statement: a direct proof of
`tripling_equation_ω₃` from `two_mul_ω₃`, never passing through the `2·ψₙ³` form, would retire the
`hy` rewrite and the `hlin` `field_simp` together — ⚠️ **leaving TWO `b`-relation residues and not
one**: `hasPreΩSqAt_three`'s `hb8` division by `4`, and `equation_of_hasPreΩSqAt`'s closing
cancellation by `4`.  ⚠️ **The first of the two is separately retirable at the `3 → 22` import
price named above and declined; the second is not** — no normalisation of `ωₙ` reaches it.  `ω₃` is
precisely the object that makes that direct route expressible.

⚠️ **The direct proof is NOT attempted here and nothing below claims it.**  It is the
`y`-coordinate analogue of `#2242`'s move, which removed the `x`-coordinate's own `4 ≠ 0` at
`e5aca61` by changing route — an `s²` cancellation in place of a `4s²` one.  ⚠️ *"This route needs
it"* is not *"no route exists"*.

**So characteristic `2` at `n = 3` is two independent questions, and this file settles the first of
them**: the `y`-coordinate numerator needs no `2` (settled here, at every commutative ring), and the
passage from the `ψ₂`-form to `Equation` does (open, and not a question about `ωₙ`).

Note that this is a purely *algebraic* on-curve identity for the classical division-polynomial
tripling coordinates; identifying `(Φ₃/Ψ₃², ω₃/ψ₃³)` with the group-law triple `3 • P` (which then
makes the on-curve property automatic) is a separate statement, not proved here but proved in
`EllipticCurves.Torsion.TriplingCoords`, which consumes `tripling_equation` below for the
nonsingularity of the tripled point.

## Main statements

* `WeierstrassCurve.Affine.tripling_equation`: the division-polynomial tripling point lies on the
  curve.
* `WeierstrassCurve.Affine.tripling_equation_ω₃`: the same, with the `y`-coordinate written
  `ω₃(x, y)/ψ₃(x, y)³` and **no `2` in the denominator**.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], Exercise 3.7, III.6.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

namespace Affine

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-- **The tripling point lies on the curve.** For a point `(x, y)` on `W` over a field of
characteristic `≠ 2`, with `ψ₃(x, y) ≠ 0` (i.e. `(x, y)` is not `3`-torsion), the point
`[3](x, y) = (Φ₃(x)/Ψ₃(x)², ω₃(x,y)/ψ₃(x,y)³)` satisfies the Weierstrass equation, where the
`3`-division `y`-coordinate value is
`ω₃(x,y) = ((2y + a₁x + a₃)·(preΨ₅(x) − preΨ₄(x)²) − a₁·Φ₃(x)·ψ₃(x,y) − a₃·ψ₃(x,y)³) / 2`.

This is the crux on-curve identity consumed by the multiplication-by-`3` function-field pullback.

⚠️ The `/2` is presentational: `tripling_equation_ω₃` below is the same statement with the
numerator's honest half `ω₃` in place of it.  The `h2` here is **not** presentational, and the
module docstring's *"two rôles"* section enumerates its **four** consumption sites and says which
rôle each plays — ⚠️ **two of the four are the `2` in this statement's own denominator.** -/
theorem tripling_equation (h : W.Equation x y) (h2 : (2 : F) ≠ 0)
    (hψ : (W.ψ 3).evalEval x y ≠ 0) :
    W.Equation ((W.Φ 3).eval x / (W.ΨSq 3).eval x)
      (((2 * y + W.a₁ * x + W.a₃) * ((W.preΨ 5).eval x - W.preΨ₄.eval x ^ 2) -
          W.a₁ * (W.Φ 3).eval x * (W.ψ 3).evalEval x y -
          W.a₃ * (W.ψ 3).evalEval x y ^ 3) /
        (2 * (W.ψ 3).evalEval x y ^ 3)) := by
  have H := equation_of_hasPreΩSqAt (hasPreΩSqAt_three h2 x) h h2 hψ
  rw [if_neg (by decide : ¬Even (3 : ℤ)), preΩ_three, eval_sub, eval_pow] at H
  have hs : (W.ψ 3).evalEval x y ^ 2 = (W.ΨSq 3).eval x := ψ_sq_evalEval h 3
  have hrw : (W.ψ 3).evalEval x y * (W.a₁ * (W.Φ 3).eval x + W.a₃ * (W.ΨSq 3).eval x) =
      W.a₁ * (W.Φ 3).eval x * (W.ψ 3).evalEval x y + W.a₃ * (W.ψ 3).evalEval x y ^ 3 := by
    rw [← hs]; ring
  rwa [hrw, ← sub_sub] at H

/-- **The tripling point lies on the curve, with no `2` in the `y`-coordinate.** For a point
`(x, y)` on `W` over a field of characteristic `≠ 2`, with `ψ₃(x, y) ≠ 0`, the point

```
[3](x, y) = (Φ₃(x)/ΨSq₃(x), ω₃(x, y)/ψ₃(x, y)³)
```

satisfies the Weierstrass equation, where `ω₃ = preΩ₃·Y + preω₃` is the **honest**
`3`-division `y`-coordinate polynomial of `EllipticCurves.Torsion.OmegaDivisionPolynomial` — a
polynomial over every commutative ring, with no division by `2` in its construction.  Unfolded by
`WeierstrassCurve.evalEval_ω₃`, the `y`-coordinate is
`(y·preΩ₃(x) + preω₃(x))/ψ₃(x, y)³`.

⚠️ **This is `tripling_equation` with the `2` gone from the STATEMENT and still present in the
HYPOTHESES**, and the module docstring's *"two rôles"* section measures why.  ⚠️ **It is not that
`h2` is consumed only by the `b`-relation rôle of the general engine**: of the four sites that rôle
accounts for two — `hasPreΩSqAt_three`'s `hb8` and the engine's closing cancellation — and the other
two are the `2` itself, the engine's `hlin` and ⚠️ **the `hy` rewrite in the
proof immediately below, which pays for a `2` this conclusion does not contain** because it routes
through `tripling_equation`.  **What this statement buys is that the expression being divided is
defined in characteristic `2`**, so the remaining question there is about `Equation` and not about
`ωₙ`. -/
theorem tripling_equation_ω₃ (h : W.Equation x y) (h2 : (2 : F) ≠ 0)
    (hψ : (W.ψ 3).evalEval x y ≠ 0) :
    W.Equation ((W.Φ 3).eval x / (W.ΨSq 3).eval x)
      (W.ω₃.evalEval x y / (W.ψ 3).evalEval x y ^ 3) := by
  have H := tripling_equation h h2 hψ
  have hs : (W.ψ 3).evalEval x y = W.Ψ₃.eval x := by rw [ψ_three]; simp [evalEval]
  have hA : (W.preΩ 3).eval x = (W.preΨ 5).eval x - W.preΨ₄.eval x ^ 2 := by
    rw [preΩ_three, eval_sub, eval_pow]
  have key : 2 * W.preω₃.eval x = (W.a₁ * x + W.a₃) * (W.preΩ 3).eval x -
      W.a₁ * (W.Φ 3).eval x * W.Ψ₃.eval x - W.a₃ * W.Ψ₃.eval x ^ 3 := by
    have h' := congrArg (Polynomial.eval x) W.two_mul_preω₃
    simpa only [eval_mul, eval_sub, eval_add, eval_pow, eval_ofNat, eval_C, eval_X] using h'
  have h3 : (W.ψ 3).evalEval x y ^ 3 ≠ 0 := pow_ne_zero 3 hψ
  have hy : ((2 * y + W.a₁ * x + W.a₃) * ((W.preΨ 5).eval x - W.preΨ₄.eval x ^ 2) -
        W.a₁ * (W.Φ 3).eval x * (W.ψ 3).evalEval x y -
        W.a₃ * (W.ψ 3).evalEval x y ^ 3) / (2 * (W.ψ 3).evalEval x y ^ 3) =
      W.ω₃.evalEval x y / (W.ψ 3).evalEval x y ^ 3 := by
    rw [evalEval_ω₃, div_eq_div_iff (mul_ne_zero h2 h3) h3, ← hA, hs]
    linear_combination (-(W.Ψ₃.eval x ^ 3)) * key
  rwa [hy] at H

end Affine

end WeierstrassCurve
