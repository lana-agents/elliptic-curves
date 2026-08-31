/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.OmegaDivisionPolynomial

/-!
# The on-curve identity for the division-polynomial coordinates, at general `n`

Mathlib leaves the `y`-coordinate division polynomials `ωₙ` as a `TODO`, so there is no statement
on the current pin that the multiplication-by-`n` coordinates `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` lie on the curve
— the *on-curve identity* that the function-field pullback `[n]∗ : F(W) → F(W)` consumes.
`EllipticCurves.Torsion.OmegaTwo` and `EllipticCurves.Torsion.OmegaThree` state it at `n = 2` and
`n = 3`; both now import this file and read off their theorems from the engine below.

This file separates that work into the part that depends on `n` and the part that does not, in
exactly the shape `EllipticCurves.Torsion.NsmulSurjective` uses for the surjectivity engine.

## The one index-dependent input

Everything reduces to a **single univariate polynomial identity** in `R[X]`, packaged as the
predicate `WeierstrassCurve.HasPreΩSq`:

```
preΩₙ² · (if Even n then 1 else Ψ₂Sq) =
  4Φₙ³ + b₂Φₙ²ΨSqₙ + 2b₄ΦₙΨSqₙ² + b₆ΨSqₙ³
```

with `preΩₙ = preΨₙ₊₂·preΨₙ₋₁² − preΨₙ₋₂·preΨₙ₊₁²` the univariate `y`-numerator of
`EllipticCurves.Torsion.OmegaDivisionPolynomial`.  It is the completed-square form of the
Weierstrass equation at the point `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)`, with all denominators cleared; the parity
factor is a degree count, since `preΩₙ` has degree `3n²/2` for even `n` but only `(3n² − 3)/2` for
odd `n`, the missing `3` being the degree of `Ψ₂Sq`.

⚠️ **`preΨ₄_sq` is literally this identity at `n = 2`**, and the `n = 3` case is literally the
same algebra that `tripling_equation` used to run inline.  Both are univariate `CommRing` facts
about `preΨ`, so both live in `EllipticCurves.Torsion.OmegaDivisionPolynomial`; the `n = 3` one is
`hasPreΩSqAt_three` below, and it is proved here exactly once.

## Main definitions

* `WeierstrassCurve.HasPreΩSq`: the identity above, as a predicate on the index `n`.
* `WeierstrassCurve.HasPreΩSqAt`: the same identity evaluated at a single `x`.  This is what the
  engine actually consumes, and it is the weaker of the two — see the note on `n = 3` below.

## Main statements

* `WeierstrassCurve.hasPreΩSq_zero`, `WeierstrassCurve.hasPreΩSq_one`,
  `WeierstrassCurve.hasPreΩSq_two`: the polynomial identity at `n = 0`, `1`, `2`, over an arbitrary
  commutative ring and in every characteristic.
* `WeierstrassCurve.HasPreΩSq.neg`: the identity is an even function of the index, so those three
  give `n ∈ {0, ±1, ±2}`.
* `WeierstrassCurve.HasPreΩSq.at`: the polynomial identity implies the evaluated one.
* `WeierstrassCurve.Affine.hasPreΩSqAt_three`: the evaluated identity at `n = 3`, over a field of
  characteristic `≠ 2`.
* `WeierstrassCurve.Affine.equation_of_hasPreΩSqAt`: **the uniform half, written once.**  Given the
  identity at `n` and at the point's own `x`, the division-polynomial coordinates at `n` satisfy the
  Weierstrass equation, over any field of characteristic `≠ 2`, at any point of `W` with
  `ψₙ(x, y) ≠ 0`.
* `WeierstrassCurve.Affine.equation_of_hasPreΩSq`: the same from the polynomial identity.

## ⚠️ What this does and does not settle

**Nothing is proved here at any index that was not already available.**  The instances are `n = 0`
and `n = 1` (both immediate), `n = 2` (the merged `preΨ₄_sq`) and `n = 3` (the algebra that the
merged `tripling_equation` used to run inline).  What the file settles is **how much is needed at a
new index, and that it is exactly one univariate identity** — no bivariate work, no hypothesis on
`(n : F)`, no algebraically closed base, and no group-law input.  `HasPreΩSq` at general `n` is the
crux left in issue `#404`.

⚠️ **Why `n = 3` is committed in the evaluated form only, and why that is a measurement rather than
a preference.**  The polynomial identity at `n = 3` is true over `ℤ` — it needs no characteristic
hypothesis — but `4b₈ = b₂b₆ − b₄²` is not available as a substitution over an arbitrary ring, so
`ring1` must be run with the `aᵢ` as atoms.  Expanded that way each side of the `n = 3` identity has
**9903 monomials in six atoms**, and the two ways of putting that to `ring1` were both measured
here:

* in `R[X]` it **does** close — `3 m 38 s` for the module elaborated in isolation — but the same
  declaration was **killed by `lake build` with exit `137`, out of memory**, and a proof that only
  survives outside the build is not a proof this file can carry;
* restated as a plain `CommRing` auxiliary lemma, to drop the polynomial-ring overhead, `ring1` was
  still climbing through **10.5 GB resident** after 90 s and was killed by hand.

With `b₂, b₄, b₆` kept as atoms and `b₈` eliminated by division by `4` the same identity has
**545 monomials** and closes in seconds — which is exactly what `hasPreΩSqAt_three` does, and
exactly why it needs a field of characteristic `≠ 2`.  The remaining characteristic-free route, a
`linear_combination` against `b_relation`, needs a cofactor that was computed here by exact
division and has **275 monomials**: a hundred-line constant with no independent meaning.  None of
the three was worth taking; the engine assumes characteristic `≠ 2` regardless, so the evaluated
form loses nothing at the point of use.

⚠️ **This is an on-curve identity for the classical division-polynomial coordinates, not a statement
about `n • P`.**  Identifying `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` with the group-law multiple is a genuinely
separate step — it is what `EllipticCurves.Torsion.DoublingCoords` and
`EllipticCurves.Torsion.TriplingCoords` do at `n = 2` and `n = 3`, and it is issue `#251` in
general.  The two `OmegaTwo`/`OmegaThree` docstrings make the same disclaimer and it is unchanged.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], Exercise 3.7, III.6.
-/

open Polynomial
open scoped Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- **The `y`-coordinate on-curve identity at index `n`**, as a predicate on `n`:

```
preΩₙ² · (if Even n then 1 else Ψ₂Sq) =
  4Φₙ³ + b₂Φₙ²ΨSqₙ + 2b₄ΦₙΨSqₙ² + b₆ΨSqₙ³
```

This is the completed-square form `(2Y + a₁X + a₃)² = 4X³ + b₂X² + 2b₄X + b₆` of the Weierstrass
equation, evaluated at the division-polynomial coordinates `X = Φₙ/ΨSqₙ` and `Y = ωₙ/ψₙ³` and
cleared of denominators; the parity factor `if Even n then 1 else Ψ₂Sq` is forced by a degree count
on `preΩₙ`.

It is the one index-dependent input of `WeierstrassCurve.Affine.equation_of_hasPreΩSq` below, and
establishing it at general `n` is the crux left in issue `#404`. -/
def HasPreΩSq (n : ℤ) : Prop :=
  W.preΩ n ^ 2 * (if Even n then 1 else W.Ψ₂Sq) =
    4 * W.Φ n ^ 3 + C W.b₂ * W.Φ n ^ 2 * W.ΨSq n + 2 * C W.b₄ * W.Φ n * W.ΨSq n ^ 2 +
      C W.b₆ * W.ΨSq n ^ 3

/-- **The `y`-coordinate on-curve identity at index `n`, evaluated at a single `x`.**  This is what
the engine consumes: the on-curve verification happens at one point, so the polynomial identity is
more than it needs.  ⚠️ It is also strictly weaker, and the difference is not academic — at `n = 3`
the evaluated form is what this tree can afford to prove; see the module docstring. -/
def HasPreΩSqAt (n : ℤ) (x : R) : Prop :=
  (W.preΩ n).eval x ^ 2 * (if Even n then 1 else W.Ψ₂Sq.eval x) =
    4 * (W.Φ n).eval x ^ 3 + W.b₂ * (W.Φ n).eval x ^ 2 * (W.ΨSq n).eval x +
      2 * W.b₄ * (W.Φ n).eval x * (W.ΨSq n).eval x ^ 2 + W.b₆ * (W.ΨSq n).eval x ^ 3

/-- **The polynomial identity gives the evaluated one at every `x`.** -/
lemma HasPreΩSq.at {W : WeierstrassCurve R} {n : ℤ} (h : W.HasPreΩSq n) (x : R) :
    W.HasPreΩSqAt n x := by
  have H := congrArg (Polynomial.eval x) h
  simpa only [HasPreΩSqAt, eval_mul, eval_pow, eval_add, eval_ofNat, eval_C,
    apply_ite (Polynomial.eval x), eval_one] using H

/-- **The identity is an even function of the index.**  `preΩ`, `Φ` and `ΨSq` are all even in `n`,
so the three instances below cover `n ∈ {0, ±1, ±2}`. -/
lemma HasPreΩSq.neg {W : WeierstrassCurve R} {n : ℤ} (h : W.HasPreΩSq n) : W.HasPreΩSq (-n) := by
  simp only [HasPreΩSq, preΩ_neg, Φ_neg, ΨSq_neg, even_neg]
  exact h

/-- **The identity at `n = 0`.**  `preΩ₀ = 2`, `Φ₀ = 1` and `ΨSq₀ = 0`, so both sides are `4`. -/
lemma hasPreΩSq_zero : W.HasPreΩSq 0 := by
  rw [HasPreΩSq, preΩ]
  norm_num

/-- **The identity at `n = 1`.**  `preΩ₁ = 1`, `Φ₁ = X` and `ΨSq₁ = 1`, so it is the definition of
`Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆`. -/
lemma hasPreΩSq_one : W.HasPreΩSq 1 := by
  rw [HasPreΩSq, preΩ, if_neg (by decide : ¬Even (1 : ℤ)), Φ_one, ΨSq_one, Ψ₂Sq]
  simp only [show (1 : ℤ) + 2 = 3 by norm_num, show (1 : ℤ) - 1 = 0 by norm_num,
    show (1 : ℤ) - 2 = -1 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num, preΨ_three, preΨ_zero,
    preΨ_two, preΨ_neg, preΨ_one]
  C_simp
  ring1

/-- **The identity at `n = 2`.**  Since `preΩ₂ = preΨ₄` and `ΨSq₂ = Ψ₂Sq`, this is exactly the
merged `WeierstrassCurve.preΨ₄_sq` of `EllipticCurves.Torsion.OmegaDivisionPolynomial`, which is
where the duplication formula's heavy algebra already lives. -/
lemma hasPreΩSq_two : W.HasPreΩSq 2 := by
  rw [HasPreΩSq, preΩ_two, if_pos even_two, ΨSq_two, mul_one]
  exact W.preΨ₄_sq

namespace Affine

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-- **The evaluated identity at `n = 3`**, over a field of characteristic `≠ 2`.

Since `preΩ₃ = preΨ₅ − preΨ₄²` and `ΨSq₃ = Ψ₃²`, this is the univariate step that
`WeierstrassCurve.Affine.tripling_equation` (`EllipticCurves.Torsion.OmegaThree`) used to run
inline, stated at a general `x` and proved here once.  ⚠️ The characteristic hypothesis is an
artefact of the proof, not of the
statement: `4b₈ = b₂b₆ − b₄²` is eliminated by dividing by `4`, which keeps `b₂`, `b₄`, `b₆` as
`ring` atoms and the normal form small.  The module docstring records what the characteristic-free
route costs. -/
lemma hasPreΩSqAt_three (h2 : (2 : F) ≠ 0) (x : F) : W.HasPreΩSqAt 3 x := by
  have h4 : (4 : F) ≠ 0 := by rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hb8 : W.b₈ = (W.b₂ * W.b₆ - W.b₄ ^ 2) / 4 := by
    rw [eq_div_iff h4]; linear_combination W.b_relation
  rw [HasPreΩSqAt, if_neg (by decide : ¬Even (3 : ℤ)), preΩ_three, preΨ_five, ΨSq_three, Φ_three]
  simp only [Ψ₃, preΨ₄, Ψ₂Sq, eval_mul, eval_add, eval_sub, eval_pow, eval_ofNat, eval_C, eval_X]
  rw [hb8]
  field_simp
  ring

set_option maxHeartbeats 1000000 in
-- The proof clears the `ψₙ`-denominators of a division at a general index and normalises the
-- resulting rational identity twice (`hlin` and `hmain`), which needs a raised heartbeat limit.
/-- **The division-polynomial coordinates at `n` lie on the curve**, given the one univariate
identity `W.HasPreΩSqAt n x` at the point's own `x`.

For a point `(x, y)` on `W` over a field of characteristic `≠ 2` with `ψₙ(x, y) ≠ 0`, the point
`(Φₙ(x)/ΨSqₙ(x), ωₙ(x, y)/ψₙ(x, y)³)` satisfies the Weierstrass equation, where the `n`-division
`y`-coordinate value is

```
ωₙ(x, y) = ((if Even n then 1 else 2y + a₁x + a₃)·preΩₙ(x) − ψₙ(x, y)·(a₁Φₙ(x) + a₃ΨSqₙ(x)))/2.
```

This is the uniform half of the on-curve identity, written once.  ⚠️ The `if Even n` in the
numerator is the same parity factor as in `HasPreΩSq`, and it is not cosmetic: for odd `n` the
"`ψ₂`-value" `2Y + a₁X + a₃` of the multiple carries a factor of `2y + a₁x + a₃`, whose square is
`Ψ₂Sq(x)`, and for even `n` it does not.  `doubling_equation` and `tripling_equation` are the
`n = 2` and `n = 3` cases, and are derived from this theorem in `EllipticCurves.Torsion.OmegaTwo`
and `EllipticCurves.Torsion.OmegaThree`; their statements stay where they are, since they are
merged public API with consumers in `FunctionField/`. -/
theorem equation_of_hasPreΩSqAt {n : ℤ} (hΩ : W.HasPreΩSqAt n x) (h : W.Equation x y)
    (h2 : (2 : F) ≠ 0) (hψ : (W.ψ n).evalEval x y ≠ 0) :
    W.Equation ((W.Φ n).eval x / (W.ΨSq n).eval x)
      (((if Even n then 1 else 2 * y + W.a₁ * x + W.a₃) * (W.preΩ n).eval x -
          (W.ψ n).evalEval x y * (W.a₁ * (W.Φ n).eval x + W.a₃ * (W.ΨSq n).eval x)) /
        (2 * (W.ψ n).evalEval x y ^ 3)) := by
  rw [HasPreΩSqAt] at hΩ
  rw [equation_iff]
  have h4 : (4 : F) ≠ 0 := by rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have ht : (2 * y + W.a₁ * x + W.a₃) ^ 2 = W.Ψ₂Sq.eval x := by
    have H := ψ_sq_evalEval h 2
    rwa [ψ_two_evalEval, ΨSq_two] at H
  -- The parity factor, packaged so that the rest of the argument runs once rather than twice:
  -- `e` is the numerator's factor and `e²` is the one in `HasPreΩSqAt`.
  obtain ⟨e, hev, hesq⟩ :
      ∃ e : F, (if Even n then (1 : F) else 2 * y + W.a₁ * x + W.a₃) = e ∧
        e ^ 2 = if Even n then 1 else W.Ψ₂Sq.eval x := by
    rcases Int.even_or_odd n with hn | hn
    · exact ⟨1, if_pos hn, by rw [if_pos hn]; ring⟩
    · have hne : ¬Even n := Int.not_even_iff_odd.mpr hn
      exact ⟨_, if_neg hne, by rw [if_neg hne]; exact ht⟩
  rw [hev]
  rw [← hesq] at hΩ
  set s := (W.ψ n).evalEval x y with hs_def
  set Φv := (W.Φ n).eval x with hΦ_def
  set Ψv := (W.ΨSq n).eval x with hΨ_def
  set Ov := (W.preΩ n).eval x with hO_def
  have hs : s ^ 2 = Ψv := ψ_sq_evalEval h n
  have hΨne : Ψv ≠ 0 := by rw [← hs]; exact pow_ne_zero 2 hψ
  set X' := Φv / Ψv with hX'
  set Y' := (e * Ov - s * (W.a₁ * Φv + W.a₃ * Ψv)) / (2 * s ^ 3) with hY'
  -- The `ψ₂`-value of the multiple: the `a₁` and `a₃` corrections in `ωₙ` cancel exactly.
  have hlin : 2 * Y' + W.a₁ * X' + W.a₃ = e * Ov / s ^ 3 := by
    rw [hY', hX', ← hs]
    field_simp
    ring
  -- The on-curve `b`-relation for the multiple.
  have hmain : (2 * Y' + W.a₁ * X' + W.a₃) ^ 2 =
      4 * X' ^ 3 + W.b₂ * X' ^ 2 + 2 * W.b₄ * X' + W.b₆ := by
    have hd : Ov ^ 2 * e ^ 2 = 4 * Φv ^ 3 + W.b₂ * Φv ^ 2 * s ^ 2 +
        2 * W.b₄ * Φv * (s ^ 2) ^ 2 + W.b₆ * (s ^ 2) ^ 3 := by rw [hs]; exact hΩ
    rw [hlin, div_pow, mul_pow, hX', ← hs]
    field_simp
    linear_combination hd
  -- Deduce the Weierstrass equation from the `b`-relation (characteristic `≠ 2`).
  rw [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hmain
  refine mul_left_cancel₀ h4 ?_
  linear_combination hmain

/-- **The division-polynomial coordinates at `n` lie on the curve**, given the polynomial identity
`W.HasPreΩSq n`.  The `HasPreΩSqAt` form above is what the proof uses; this is the shape a
general-`n` theorem would be stated in. -/
theorem equation_of_hasPreΩSq {n : ℤ} (hΩ : W.HasPreΩSq n) (h : W.Equation x y) (h2 : (2 : F) ≠ 0)
    (hψ : (W.ψ n).evalEval x y ≠ 0) :
    W.Equation ((W.Φ n).eval x / (W.ΨSq n).eval x)
      (((if Even n then 1 else 2 * y + W.a₁ * x + W.a₃) * (W.preΩ n).eval x -
          (W.ψ n).evalEval x y * (W.a₁ * (W.Φ n).eval x + W.a₃ * (W.ΨSq n).eval x)) /
        (2 * (W.ψ n).evalEval x y ^ 3)) :=
  equation_of_hasPreΩSqAt (HasPreΩSq.at hΩ x) h h2 hψ

end Affine

end WeierstrassCurve
