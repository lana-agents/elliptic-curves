/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.DoublingSurjective

/-!
# Multiplication by `3` is surjective on `E(F̄)`

For an elliptic curve `W : Affine F` over an **algebraically closed** field `F` with `(2 : F) ≠ 0`,
every point of `W` is three times another point:

```
∀ Q : W.Point, ∃ P : W.Point, 3 • P = Q.
```

This is the `n = 3` analogue of `EllipticCurves.Torsion.DoublingSurjective`'s
`nsmul_two_surjective`, which was the *only* surjectivity result for the group law in this tree.
Like it, the proof is elementary and one-dimensional: it solves the tripling equation for the
`x`-coordinate directly, and is independent of Ward's theorem, of the elliptic-net recurrence, and
of the general multiplication-by-`n` coordinate formula.

## Which characteristic hypotheses are load-bearing

**Only `(2 : F) ≠ 0`.  `(3 : F) ≠ 0` is *not* needed**, and is deliberately absent.

* `h2` is used in exactly three places, none of them the tripling formula as such: `exists_equation`
  (finding a point above a given `x` means solving a quadratic in `y`),
  `Ψ₂Sq_eval_ne_zero_of_root_Ψ₃`, and the `2` in the denominator of the tangent slope, which is what
  makes `addX_add_self_mul_ΨSq_three_eval` fail in characteristic `2`.
* A `(3 : F) ≠ 0` would be needed to know `deg Ψ₃ = 4`, but nothing here needs that: the degree
  input is `deg Φ₃ = 9` with leading coefficient `1` (Mathlib's `natDegree_Φ` / `coeff_Φ`, valid
  over
  any nontrivial ring) against `deg ΨSq₃ ≤ 8` (`natDegree_ΨSq_le`, unconditional).  In
  characteristic `3` the polynomial `Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈` degenerates to
  `b₂X³ + b₈`, and every statement below still holds.

This is stronger than expected — issue `#690` predicted `h3` would be inherited from the tripling
formula — and it is the right answer: `[n]` is surjective on `E(F̄)` for every `n ≥ 1` and every
characteristic.

## The mechanism

Write `p = Ψ₂Sq(x)`, `T = Ψ₃(x)`, `Q = preΨ₄(x)` for an affine point `P = (x, y)`.

* **The tripling formula with denominators cleared**, `addX_add_self_mul_ΨSq_three_eval`:
  for `y ≠ negY x y` and `T ≠ 0`,

  ```
  x(3P) · ΨSq₃(x) = Φ₃(x).
  ```

  This is the only substantial computation.  It is the affine-point mirror of
  `EllipticCurves.FunctionField.GenericTripling`'s `addX_gen_eq_mulByThree`, which proves the same
  identity at the generic point of `F(W)`; that statement cannot be specialised to an `F`-point
  (there is no ring map `F(W) → F`), so the computation is redone here, in the same shape.  The
  route: `x(2P) − x = −T/p` (`addX_self_sub`, merged) and `y(2P) − y = (Q − p² + a₁Ts)/(2ps)` give
  the secant slope `(p² − Q − a₁Ts)/(2sT)` through `2P` and `P`, and substituting it into `addX`
  reduces the identity to `tripling_core`, a single univariate division-polynomial relation closed
  off the `b`-relation.

* **`Φ₃` and `Ψ₃` have no common root**, `Φ_three_eval_ne_zero_of_Ψ₃`.  At a root of `Ψ₃` the core
  relation collapses to `(p² + Q)² = 0`, so `Q = −p²` and therefore `Φ₃(x) = x·0 − Q·p = p³`, which
  is nonzero because a root of `Ψ₃` is never a root of `Ψ₂Sq` (`Ψ₂Sq_eval_ne_zero_of_root_Ψ₃`,
  merged).  **No resultant computation and no Bézout certificate for `(Φ₃, Ψ₃)` is needed** — the
  `n = 3` mirror of the same economy in `DoublingSurjective`.

Given a target `x₀`, the polynomial `Φ₃ − x₀·ΨSq₃` is monic of degree `9`, so over `F̄` it has a
root `x₁`, at which `Ψ₃` is nonzero by the previous point.  Take any `P = (x₁, y₁)` above it.

⚠️ **`P` may be `2`-torsion, and that case is not degenerate — it is a second, genuine branch.**
`Ψ₂Sq(x₁) = 0` is not excluded (only `Ψ₃(x₁) ≠ 0` is), and there `2P = O`, so the secant
construction of `3P = 2P + P` does not apply.  But then `Φ₃(x₁) = x₁·T²` and `ΨSq₃(x₁) = T²`, so the
defining equation forces `x₁ = x₀` outright, and `3P = P` already has `x`-coordinate `x₀`.  Both
branches end with `3P` affine of `x`-coordinate `x₀`, whence `3P = ±Q` by `Point.X_eq_iff`, and `−P`
handles the sign.

## Main statements

* `WeierstrassCurve.Affine.preΨ₄_eq` / `preΨ₄_eval` — `preΨ₄ = Ψ₃·(6X² + b₂X + b₄) − Ψ₂Sq²`, an
  identity of division polynomials that needs the `b`-relation and is what makes the `y`-coordinate
  of `2P` computable in closed form;
* `WeierstrassCurve.Affine.tripling_core` — the core relation
  `(p² − Q)² + 4T³ − (b₂ + 12x)·p·T² + 4Qp² = 0`;
* `WeierstrassCurve.Affine.Φ_three_eval_ne_zero_of_Ψ₃` — `Φ₃` and `Ψ₃` have no common root;
* `WeierstrassCurve.Affine.exists_eval_Φ_three_eq` — every `x₀` solves `Φ₃(x) = x₀·ΨSq₃(x)`;
* `WeierstrassCurve.Affine.addX_add_self_mul_ΨSq_three_eval` — the tripling formula
  `x(3P)·ΨSq₃(x) = Φ₃(x)`;
* `WeierstrassCurve.Affine.exists_nsmul_three_some` — every `x₀` is the `x`-coordinate of a tripled
  point;
* **`WeierstrassCurve.Affine.exists_nsmul_three_eq`** and
  **`WeierstrassCurve.Affine.nsmul_three_surjective`** — the headline.

## Scope

`DoublingSurjective.lean` is not edited.  Nothing here is about `#E[3] = 9`
(`Torsion/ThreeTorsionStructure.lean` has that), about the Weil pairing, or about general `[n]`:
the classical route to `[n]`-surjectivity is Silverman III.4.10 through `deg [n] = n²`, which is
rung-8 territory and a different piece of work.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.
-/

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-! ## Division-polynomial identities -/

/-- The `b`-relation `4b₈ = b₂b₆ − b₄²` pushed into `F[X]`, the form `linear_combination` needs
when the goal is an identity of polynomials rather than of scalars. -/
private lemma C_b_relation : (4 : F[X]) * C W.b₈ = C W.b₂ * C W.b₆ - C W.b₄ ^ 2 := by
  simpa [map_ofNat] using congrArg C W.b_relation

/-- **`preΨ₄ = Ψ₃·(6X² + b₂X + b₄) − Ψ₂Sq²`.**

The `b`'s are not algebraically independent, and this identity is one of the places where that
matters: its `X²` coefficient is `10b₈` on the left and `6b₈ + b₂b₆ − b₄²` on the right, so the
`b`-relation `4b₈ = b₂b₆ − b₄²` is exactly what closes it.  A bare `ring` will not prove it.

Its role below: `2·(3x² + 2a₂x + a₄ − a₁y) + a₁·(2y + a₁x + a₃) = 6x² + b₂x + b₄` is `y`-free, so
this identity is what turns the `y`-coordinate of the doubled point into a function of `x` alone. -/
lemma preΨ₄_eq :
    W.preΨ₄ = W.Ψ₃ * (6 * X ^ 2 + C W.b₂ * X + C W.b₄) - W.Ψ₂Sq ^ 2 := by
  rw [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₃, WeierstrassCurve.Ψ₂Sq]
  simp only [map_ofNat, C_sub, C_mul, C_pow]
  linear_combination (norm := ring1) (X : F[X]) ^ 2 * C_b_relation (W := W)

/-- `preΨ₄_eq`, evaluated. -/
lemma preΨ₄_eval (x : F) :
    W.preΨ₄.eval x = W.Ψ₃.eval x * (6 * x ^ 2 + W.b₂ * x + W.b₄) - W.Ψ₂Sq.eval x ^ 2 := by
  rw [preΨ₄_eq]; simp

/-- Mathlib's `Φ_three : Φ₃ = X·Ψ₃² − preΨ₄·Ψ₂Sq`, evaluated. -/
lemma Φ_three_eval (x : F) :
    (W.Φ 3).eval x = x * W.Ψ₃.eval x ^ 2 - W.preΨ₄.eval x * W.Ψ₂Sq.eval x := by
  rw [WeierstrassCurve.Φ_three]; simp

/-- Mathlib's `ΨSq_three : ΨSq₃ = Ψ₃²`, evaluated. -/
lemma ΨSq_three_eval (x : F) : (W.ΨSq 3).eval x = W.Ψ₃.eval x ^ 2 := by
  rw [WeierstrassCurve.ΨSq_three]; simp

/-- **The core division-polynomial relation.**  Writing `p = Ψ₂Sq(x)`, `T = Ψ₃(x)`,
`Q = preΨ₄(x)`,

```
(p² − Q)² + 4T³ − (b₂ + 12x)·p·T² + 4Qp² = 0.
```

It is the identity the tripling formula reduces to once the doubling denominators are cleared, and
it is also what shows `Φ₃` and `Ψ₃` have no common root.  Like `preΨ₄_eq` it is closed off the
`b`-relation.  (The same relation, at the generic point, is the `hcore` step of
`EllipticCurves.FunctionField.GenericTripling`; the `linear_combination` witness is shared.) -/
lemma tripling_core (x : F) :
    (W.Ψ₂Sq.eval x ^ 2 - W.preΨ₄.eval x) ^ 2 + 4 * W.Ψ₃.eval x ^ 3
        - (W.b₂ + 12 * x) * W.Ψ₂Sq.eval x * W.Ψ₃.eval x ^ 2
        + 4 * W.preΨ₄.eval x * W.Ψ₂Sq.eval x ^ 2 = 0 := by
  rw [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄]
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_ofNat]
  linear_combination (W.b₈ ^ 2 + 6 * x * W.b₆ * W.b₈ + 9 * x ^ 2 * W.b₆ ^ 2 +
      8 * x ^ 2 * W.b₄ * W.b₈ + 24 * x ^ 3 * W.b₄ * W.b₆ + 4 * x ^ 3 * W.b₂ * W.b₈ +
      22 * x ^ 4 * W.b₈ + 16 * x ^ 4 * W.b₄ ^ 2 + 11 * x ^ 4 * W.b₂ * W.b₆ +
      54 * x ^ 5 * W.b₆ + 14 * x ^ 5 * W.b₂ * W.b₄ + 60 * x ^ 6 * W.b₄ +
      3 * x ^ 6 * W.b₂ ^ 2 + 24 * x ^ 7 * W.b₂ + 45 * x ^ 8) * W.b_relation

/-! ## `Φ₃` and `Ψ₃` have no common root -/

/-- At a root of `Ψ₃` the core relation collapses to `(p² + Q)² = 0`, so `Q = −p²`. -/
lemma preΨ₄_eval_of_Ψ₃ {x : F} (hT : W.Ψ₃.eval x = 0) :
    W.preΨ₄.eval x = -W.Ψ₂Sq.eval x ^ 2 := by
  have hcore := tripling_core (W := W) x
  rw [hT] at hcore
  have hsq : (W.Ψ₂Sq.eval x ^ 2 + W.preΨ₄.eval x) ^ 2 = 0 := by linear_combination hcore
  have h0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  linear_combination h0

/-- At a root of `Ψ₃` one has `Φ₃(x) = Ψ₂Sq(x)³`. -/
lemma Φ_three_eval_of_Ψ₃ {x : F} (hT : W.Ψ₃.eval x = 0) :
    (W.Φ 3).eval x = W.Ψ₂Sq.eval x ^ 3 := by
  rw [Φ_three_eval, hT, preΨ₄_eval_of_Ψ₃ hT]; ring

/-- **`Φ₃` and `Ψ₃` have no common root.**  A root of `Ψ₃` is never a root of `Ψ₂Sq`
(`Ψ₂Sq_eval_ne_zero_of_root_Ψ₃`, merged), and there `Φ₃(x) = Ψ₂Sq(x)³`.  No Bézout certificate for
the pair `(Φ₃, Ψ₃)` is needed. -/
lemma Φ_three_eval_ne_zero_of_Ψ₃ [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) {x : F}
    (hT : W.Ψ₃.eval x = 0) : (W.Φ 3).eval x ≠ 0 := by
  rw [Φ_three_eval_of_Ψ₃ hT]
  exact pow_ne_zero 3 (Ψ₂Sq_eval_ne_zero_of_root_Ψ₃ h2 hT)

/-! ## Solving the tripling equation for the `x`-coordinate -/

/-- The auxiliary polynomial `Φ₃ − x₀·ΨSq₃` is monic of degree `9`: `Φ₃` is monic of degree `9`
while `ΨSq₃` has degree at most `8`.  **No hypothesis on `(3 : F)`**: both facts are unconditional
in Mathlib. -/
lemma natDegree_Φ_three_sub_C_mul_ΨSq_three (x₀ : F) :
    (W.Φ 3 - C x₀ * W.ΨSq 3).natDegree = 9 := by
  have hΦ : (W.Φ 3).natDegree = 9 := by simpa using W.natDegree_Φ 3
  have hΨ : (C x₀ * W.ΨSq 3).natDegree < 9 :=
    lt_of_le_of_lt ((natDegree_C_mul_le x₀ (W.ΨSq 3)).trans (W.natDegree_ΨSq_le 3)) (by norm_num)
  rw [natDegree_sub_eq_left_of_natDegree_lt (hΦ ▸ hΨ), hΦ]

/-- **Every value of `x` solves the tripling equation.**  Over an algebraically closed field the
degree-`9` polynomial `Φ₃ − x₀·ΨSq₃` has a root. -/
lemma exists_eval_Φ_three_eq [IsAlgClosed F] (x₀ : F) :
    ∃ x : F, (W.Φ 3).eval x = x₀ * (W.ΨSq 3).eval x := by
  have hdeg : (W.Φ 3 - C x₀ * W.ΨSq 3).degree ≠ 0 :=
    (natDegree_pos_iff_degree_pos.mp
      (by rw [natDegree_Φ_three_sub_C_mul_ΨSq_three]; norm_num)).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdeg
  rw [IsRoot.def, eval_sub, eval_mul, eval_C, sub_eq_zero] at hx
  exact ⟨x, hx⟩


/-! ## The tripling formula `x(3P) = Φ₃(x) / ΨSq₃(x)` -/

section Point

variable [DecidableEq F]

set_option maxHeartbeats 4000000 in
-- The tripling identity clears the doubling denominators into a large division-polynomial relation;
-- its `linear_combination`/`ring1` normalisation exceeds both the default heartbeat limit and the
-- default recursion depth.  The same computation at the generic point (`GenericTripling.lean`) also
-- runs with a raised heartbeat limit.
set_option maxRecDepth 100000 in
/-- **The tripling formula at an affine point, with the denominator cleared.**  For an affine point
`P = (x, y)` of `W` not fixed by negation and with `Ψ₃(x) ≠ 0` — equivalently, with `2P ≠ ±P`, so
that `3P = 2P + P` takes the secant branch — the `x`-coordinate of `3P` satisfies

```
x(3P) · ΨSq₃(x) = Φ₃(x).
```

This is the `n = 3` instance of the multiplication-by-`n` coordinate formula
`x(nP) = Φₙ(x)/ΨSqₙ(x)`, in a form that needs no division; the general case is not available in this
tree.  The mirror statement at the generic point of `F(W)` is
`EllipticCurves.FunctionField.GenericTripling.addX_gen_eq_mulByThree`; it cannot be specialised to
an `F`-point, so the computation is redone here.

Characteristic `2` is excluded (`h2`), through the tangent slope; nothing needs `(3 : F) ≠ 0`. -/
theorem addX_add_self_mul_ΨSq_three_eval (h2 : (2 : F) ≠ 0) {x y : F} (h : W.Equation x y)
    (hy : y ≠ W.negY x y) (hT : W.Ψ₃.eval x ≠ 0) :
    W.addX (W.addX x x (W.slope x x y y)) x
        (W.slope (W.addX x x (W.slope x x y y)) x (W.addY x x y (W.slope x x y y)) y)
        * (W.ΨSq 3).eval x = (W.Φ 3).eval x := by
  set ℓ := W.slope x x y y with hℓ
  set x₂ := W.addX x x ℓ with hx₂
  set y₂ := W.addY x x y ℓ with hy₂def
  set s := 2 * y + W.a₁ * x + W.a₃ with hsdef
  set T := W.Ψ₃.eval x with hTdef
  set Q := W.preΨ₄.eval x with hQdef
  have hsne : s ≠ 0 := two_mul_add_ne_zero_of_Y_ne hy
  have hs : W.Ψ₂Sq.eval x = s ^ 2 := Ψ₂Sq_eval_eq_sq h
  have hXsub : (x₂ - x) * s ^ 2 = -T := by
    rw [hx₂, hℓ, addX_self_sub h hy, div_mul_cancel₀ _ (pow_ne_zero 2 hsne)]
  have hx₂ne : x₂ - x ≠ 0 := by
    intro hcon
    rw [hcon, zero_mul, eq_comm, neg_eq_zero] at hXsub
    exact hT hXsub
  have hslope_self : ℓ * s = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := slope_self_mul hy
  have hQeq : Q = T * (6 * x ^ 2 + (W.a₁ ^ 2 + 4 * W.a₂) * x + (2 * W.a₄ + W.a₁ * W.a₃))
      - (s ^ 2) ^ 2 := by
    rw [hQdef, hTdef, preΨ₄_eval, hs, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  have hcore : ((s ^ 2) ^ 2 - Q) ^ 2 + 4 * T ^ 3
      - ((W.a₁ ^ 2 + 4 * W.a₂) + 12 * x) * s ^ 2 * T ^ 2 + 4 * Q * (s ^ 2) ^ 2 = 0 := by
    have := tripling_core (W := W) x
    rw [hs, ← hTdef, ← hQdef, WeierstrassCurve.b₂] at this
    exact this
  have hYkey : (y₂ - y) * (2 * s ^ 2 * s) = Q - (s ^ 2) ^ 2 + W.a₁ * T * s := by
    rw [hy₂def, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, ← hx₂]
    linear_combination (-2 * s * (ℓ + W.a₁)) * hXsub + (2 * T) * hslope_self
      + (-1 : F) * hQeq
  set L := W.slope x₂ x y₂ y with hLdef
  have hsl : L * (x₂ - x) = y₂ - y := by
    rw [hLdef, slope_of_X_ne (fun hcon => hx₂ne (by rw [hcon, sub_self])), div_mul_cancel₀ _ hx₂ne]
  have hslope2 : L * (2 * s * T) = (s ^ 2) ^ 2 - Q - W.a₁ * T * s := by
    linear_combination (-2 * s ^ 2 * s) * hsl + (-1 : F) * hYkey + (2 * s * L) * hXsub
  have h4 : (4 : F) * s ^ 2 ≠ 0 := by
    refine mul_ne_zero ?_ (pow_ne_zero 2 hsne)
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have main : (W.addX x₂ x L * T ^ 2 - (x * T ^ 2 - Q * s ^ 2)) * (4 * s ^ 2) = 0 := by
    simp only [WeierstrassCurve.Affine.addX]
    linear_combination (2 * s * T * L + s ^ 4 - Q + W.a₁ * T * s) * hslope2
      + (-4 * T ^ 2) * hXsub + hcore
  rw [ΨSq_three_eval, Φ_three_eval, ← hTdef, ← hQdef, hs]
  have hz := (mul_eq_zero.mp main).resolve_right h4
  linear_combination hz

/-- **Every `x`-coordinate is the `x`-coordinate of a tripled point.**  Over an algebraically closed
field of characteristic `≠ 2`, for every `x₀` there is a point `P` with `3 • P` affine of
`x`-coordinate `x₀`.

Two branches, both genuine: if the point `P = (x, y)` produced above the root of `Φ₃ − x₀·ΨSq₃` is
`2`-torsion then `3P = P` and the defining equation forces `x = x₀` directly; otherwise
`3P = 2P + P`
is the secant sum and `addX_add_self_mul_ΨSq_three_eval` computes its `x`-coordinate. -/
theorem exists_nsmul_three_some [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) (x₀ : F) :
    ∃ (P : W.Point) (y' : F) (h' : W.Nonsingular x₀ y'), (3 : ℕ) • P = Point.some x₀ y' h' := by
  obtain ⟨x, hx⟩ := exists_eval_Φ_three_eq (W := W) x₀
  have hT : W.Ψ₃.eval x ≠ 0 := by
    intro h0
    refine Φ_three_eval_ne_zero_of_Ψ₃ h2 h0 ?_
    rw [hx, ΨSq_three_eval, h0]; ring
  obtain ⟨y, hyeq⟩ := exists_equation (W := W) h2 x
  have hns : W.Nonsingular x y := equation_iff_nonsingular.mp hyeq
  have h3P : (3 : ℕ) • Point.some x y hns
      = Point.some x y hns + Point.some x y hns + Point.some x y hns := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, add_smul, two_nsmul, one_nsmul]
  by_cases hyne : y = W.negY x y
  · -- `P` is `2`-torsion: `3 • P = P`, and the equation forces `x = x₀`
    have hs0 : 2 * y + W.a₁ * x + W.a₃ = 0 := by
      have h' := hyne
      rw [WeierstrassCurve.Affine.negY] at h'
      linear_combination h'
    have hp : W.Ψ₂Sq.eval x = 0 := by
      rw [Ψ₂Sq_eval_eq_sq hyeq, hs0]; ring
    have hxx : x = x₀ := by
      have hΦ := Φ_three_eval (W := W) x
      rw [hp, mul_zero, sub_zero, hx, ΨSq_three_eval] at hΦ
      exact mul_right_cancel₀ (pow_ne_zero 2 hT) hΦ.symm
    subst hxx
    exact ⟨Point.some x y hns, y, hns, by
      rw [h3P, Point.add_self_of_Y_eq hyne, zero_add]⟩
  · -- the generic case: `3 • P = 2 • P + P` is affine with `x`-coordinate `x₀`
    have hx₂ne : W.addX x x (W.slope x x y y) ≠ x := by
      rw [Ne, addX_self_eq_iff hyeq hyne]
      exact hT
    have hkey := addX_add_self_mul_ΨSq_three_eval h2 hyeq hyne hT
    rw [hx, ΨSq_three_eval] at hkey
    have hX : W.addX (W.addX x x (W.slope x x y y)) x
        (W.slope (W.addX x x (W.slope x x y y)) x (W.addY x x y (W.slope x x y y)) y) = x₀ :=
      mul_right_cancel₀ (pow_ne_zero 2 hT) hkey
    have hns₃ : W.Nonsingular
        (W.addX (W.addX x x (W.slope x x y y)) x
          (W.slope (W.addX x x (W.slope x x y y)) x (W.addY x x y (W.slope x x y y)) y))
        (W.addY (W.addX x x (W.slope x x y y)) x (W.addY x x y (W.slope x x y y))
          (W.slope (W.addX x x (W.slope x x y y)) x (W.addY x x y (W.slope x x y y)) y)) :=
      nonsingular_add (nonsingular_add hns hns fun hxy => hyne hxy.right) hns
        fun hxy => hx₂ne hxy.left
    refine ⟨Point.some x y hns,
      W.addY (W.addX x x (W.slope x x y y)) x (W.addY x x y (W.slope x x y y))
        (W.slope (W.addX x x (W.slope x x y y)) x (W.addY x x y (W.slope x x y y)) y),
      hX ▸ hns₃, ?_⟩
    rw [h3P, Point.add_self_of_Y_ne hyne, Point.add_of_X_ne hx₂ne]
    simp only [Point.some.injEq, and_true]
    exact hX

/-- **Multiplication by `3` is surjective on `E(F̄)`.**  Over an algebraically closed field of
characteristic `≠ 2`, every point of an elliptic curve is three times another point.  The point at
infinity is `3 • 0`; an affine `Q` is matched by `exists_nsmul_three_some`, which pins the
`x`-coordinate, leaving the sign ambiguity `3P = ±Q` that `Point.X_eq_iff` resolves and `−P`
absorbs. -/
theorem exists_nsmul_three_eq [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) (Q : W.Point) :
    ∃ P : W.Point, (3 : ℕ) • P = Q := by
  rcases Q with _ | ⟨x₀, y₀, hQ⟩
  · exact ⟨0, smul_zero 3⟩
  · obtain ⟨P, y', h', hP⟩ := exists_nsmul_three_some (W := W) h2 x₀
    rcases (Point.X_eq_iff (h₁ := h') (h₂ := hQ)).mp rfl with hc | hc
    · exact ⟨P, by rw [hP, hc]⟩
    · exact ⟨-P, by rw [smul_neg, hP, hc, neg_neg]⟩

/-- **Multiplication by `3` is surjective on `E(F̄)`**, stated as `Function.Surjective` — the
`n = 3` analogue of `nsmul_two_surjective`, and the form `Torsion/Divisible.lean`'s
`torsionSmulHom_surjective` consumes. -/
theorem nsmul_three_surjective [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) :
    Function.Surjective fun P : W.Point => (3 : ℕ) • P :=
  exists_nsmul_three_eq h2

/-! ### Non-vacuity

The tripling formula carries three hypotheses at once — the point is on the curve, is not fixed by
negation, and has `Ψ₃(x) ≠ 0` — so it is worth exhibiting a point satisfying all three.  On
`y² = x³ + 1` over `ℚ` the point `(2, 3)` does: `negY 2 3 = −3 ≠ 3`, and
`Ψ₃(2) = 3·16 + 3·4·2 = 72`.

(The surjectivity statements themselves need an algebraically closed base field; as with the merged
`nsmul_two_surjective`, no committed instantiation is attempted here.) -/

section Nonvacuity

/-- The curve `y² = x³ + 1` over `ℚ`, of discriminant `-432`. -/
private def exampleCurve : Affine ℚ := ⟨0, 0, 0, 0, 1⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

example : exampleCurve.Equation 2 3 ∧ (3 : ℚ) ≠ exampleCurve.negY 2 3
    ∧ exampleCurve.Ψ₃.eval 2 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff]
  · norm_num [exampleCurve, WeierstrassCurve.Affine.negY]
  · norm_num [exampleCurve, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]

end Nonvacuity

end Point

end WeierstrassCurve.Affine
