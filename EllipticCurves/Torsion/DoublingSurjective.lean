/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.DivisionPolynomial.Coprime
import EllipticCurves.Torsion.ThreeTorsionStructure

/-!
# Multiplication by `2` is surjective on `E(F̄)`

For an elliptic curve `W : Affine F` over an **algebraically closed** field `F` with `(2 : F) ≠ 0`,
every point of `W` is twice another point:

```
∀ Q : W.Point, ∃ P : W.Point, 2 • P = Q.
```

Silverman deduces this from the general fact that a nonconstant morphism of smooth projective curves
is surjective (*AEC*, II.2.3 and III.4.10). The proof here is elementary and entirely
one-dimensional: it solves the doubling equation for the `x`-coordinate directly. In particular
it is **independent of Ward's theorem, of the elliptic-net recurrence, and of the general
multiplication-by-`n` coordinate formula `x(nP) = Φₙ(x)/ΨSqₙ(x)`**, which is what gates the
analogous statement for `n ≠ 2`.

## The mechanism

Two inputs, both already available.

* **The doubling formula at `n = 2`, with denominators cleared.** For an affine point `(x, y)` of
  `W` not fixed by negation, `EllipticCurves.Torsion.ThreeTorsion` gives the tangent-line defect
  `x(2P) - x = -Ψ₃(x) / (2y + a₁x + a₃)²`, and `EllipticCurves.Torsion.TwoTorsion` gives
  `Ψ₂Sq.eval x = (2y + a₁x + a₃)²`. Since `Φ₂ = X · Ψ₂Sq - Ψ₃`
  (`WeierstrassCurve.Φ_two_eq`, `EllipticCurves.DivisionPolynomial.Coprime`), these give

  ```
  x(2P) · Ψ₂Sq.eval x = Φ₂.eval x                                       (`addX_self_mul_Ψ₂Sq_eval`)
  ```

  — the `n = 2` instance of `x(nP) = Φₙ(x)/ΨSqₙ(x)`, in a form that needs no division.

* **`Φ₂` and `Ψ₂Sq` have no common root.** A common root `x` would be a root of
  `Ψ₃ = X · Ψ₂Sq - Φ₂` as well, and `EllipticCurves.Torsion.ThreeTorsionStructure` shows that a root
  of `Ψ₃` is never a root of `Ψ₂Sq` (`Ψ₂Sq_eval_ne_zero_of_root_Ψ₃`): the point above it would have
  both partial derivatives of the Weierstrass polynomial vanishing. **No resultant computation and
  no identity of the form `A · Φ₂ + B · Ψ₂Sq = Δ` is needed.**

Given a target `Q = (x₀, y₀)`, the polynomial `Φ₂ - C x₀ · Ψ₂Sq` is monic of degree `4`, because
`Φ₂` is monic of degree `4` (`WeierstrassCurve.natDegree_Φ`) while `Ψ₂Sq` has degree at most `3`. So
over an algebraically closed field it has a root `x₁`, and then `Ψ₂Sq.eval x₁ ≠ 0` by the second
input. Any point `P = (x₁, y₁)` above `x₁` — one exists by `exists_equation` — therefore satisfies
`y₁ ≠ negY x₁ y₁`, so `2 • P` is affine with `x(2 • P) = x₀`. Hence `2 • P = ±Q`, and replacing `P`
by `-P` in the second case finishes. The point at infinity is `2 • 0`.

No hypothesis on `(3 : F)` is used anywhere.

## Main statements

* `WeierstrassCurve.Affine.addX_self_mul_Ψ₂Sq_eval`: the doubling formula `x(2P) · Ψ₂Sq(x) = Φ₂(x)`.
* `WeierstrassCurve.Affine.exists_addX_self_eq`: every `x₀` is `x(2P)` for some affine point `P` not
  fixed by negation.
* `WeierstrassCurve.Affine.exists_nsmul_two_eq`, `WeierstrassCurve.Affine.nsmul_two_surjective`:
  multiplication by `2` is surjective on `E(F̄)`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4, Corollary 4.9 and
  III.6, Corollary 6.4.
-/

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-! ## The `Φ₂` dictionary -/

/-- The pointwise form of `Φ_two_eq`. -/
lemma Ψ₃_eval_eq_sub (x : F) : W.Ψ₃.eval x = x * W.Ψ₂Sq.eval x - (W.Φ 2).eval x := by
  rw [Φ_two_eq]
  simp only [eval_sub, eval_mul, eval_X]
  ring

/-- The pointwise form of `Φ_two_eq`, solved for `Φ₂`. -/
lemma Φ_two_eval (x : F) : (W.Φ 2).eval x = x * W.Ψ₂Sq.eval x - W.Ψ₃.eval x := by
  rw [Ψ₃_eval_eq_sub]
  ring

/-! ## Solving the doubling equation for the `x`-coordinate -/

/-- The auxiliary polynomial `Φ₂ - x₀ · Ψ₂Sq`, whose roots are the `x`-coordinates of the points `P`
with `x(2P) = x₀`, is monic of degree `4`: `Φ₂` is monic of degree `4` while `Ψ₂Sq` has degree at
most `3`. -/
lemma natDegree_Φ_two_sub_C_mul_Ψ₂Sq (x₀ : F) :
    (W.Φ 2 - C x₀ * W.Ψ₂Sq).natDegree = 4 := by
  have hΦ : (W.Φ 2).natDegree = 4 := by simpa using W.natDegree_Φ 2
  have hΨ : (C x₀ * W.Ψ₂Sq).natDegree < 4 :=
    lt_of_le_of_lt ((natDegree_C_mul_le x₀ W.Ψ₂Sq).trans W.natDegree_Ψ₂Sq_le) (by norm_num)
  rw [natDegree_sub_eq_left_of_natDegree_lt (hΦ ▸ hΨ), hΦ]

/-- **Every value of `x` is the `x`-coordinate of a doubled point.** Over an algebraically closed
field the quartic `Φ₂ - x₀ · Ψ₂Sq` has a root. -/
lemma exists_eval_Φ_two_eq [IsAlgClosed F] (x₀ : F) :
    ∃ x : F, (W.Φ 2).eval x = x₀ * W.Ψ₂Sq.eval x := by
  have hdeg : (W.Φ 2 - C x₀ * W.Ψ₂Sq).degree ≠ 0 :=
    (natDegree_pos_iff_degree_pos.mp
      (by rw [natDegree_Φ_two_sub_C_mul_Ψ₂Sq]; norm_num)).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdeg
  rw [IsRoot.def, eval_sub, eval_mul, eval_C, sub_eq_zero] at hx
  exact ⟨x, hx⟩

/-! ## The doubling formula `x(2P) = Φ₂(x) / Ψ₂Sq(x)` -/

variable [DecidableEq F]

/-- **The doubling formula at `n = 2`, with the denominator cleared.** For an affine point `(x, y)`
of `W` not fixed by negation, the `x`-coordinate of `2 • (x, y)` is `Φ₂(x) / Ψ₂Sq(x)`.

This is the `n = 2` instance of the multiplication-by-`n` coordinate formula
`x(nP) = Φₙ(x) / ΨSqₙ(x)`; the general case is not available, but doubling is computed in closed
form by the tangent line. -/
lemma addX_self_mul_Ψ₂Sq_eval {x y : F} (h : W.Equation x y) (hy : y ≠ W.negY x y) :
    W.addX x x (W.slope x x y y) * W.Ψ₂Sq.eval x = (W.Φ 2).eval x := by
  have hd : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := two_mul_add_ne_zero_of_Y_ne hy
  have key : (W.addX x x (W.slope x x y y) - x) * (2 * y + W.a₁ * x + W.a₃) ^ 2
      = -W.Ψ₃.eval x := by
    rw [addX_self_sub h hy, div_mul_cancel₀ _ (pow_ne_zero 2 hd)]
  rw [Φ_two_eval, Ψ₂Sq_eval_eq_sq h]
  linear_combination key

/-- The `x`-coordinate solution, packaged with a point above it. Over an algebraically closed field
of characteristic `≠ 2`, for every `x₀` there is an affine point `(x, y)` of `W`, not fixed by
negation, with `x(2 • (x, y)) = x₀`. -/
lemma exists_addX_self_eq [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) (x₀ : F) :
    ∃ x y : F, W.Nonsingular x y ∧ y ≠ W.negY x y ∧
      W.addX x x (W.slope x x y y) = x₀ := by
  obtain ⟨x, hx⟩ := exists_eval_Φ_two_eq (W := W) x₀
  have hne : W.Ψ₂Sq.eval x ≠ 0 := by
    intro h0
    have hΦ : (W.Φ 2).eval x = 0 := by rw [hx, h0, mul_zero]
    exact Ψ₂Sq_eval_ne_zero_of_root_Ψ₃ h2 (by rw [Ψ₃_eval_eq_sub, h0, hΦ]; ring) h0
  obtain ⟨y, hy⟩ := exists_equation (W := W) h2 x
  have hns : W.Nonsingular x y := equation_iff_nonsingular.mp hy
  have hyne : y ≠ W.negY x y := by
    intro hcon
    have hd : 2 * y + W.a₁ * x + W.a₃ = 0 := by
      rw [negY] at hcon
      linear_combination hcon
    exact hne (by rw [Ψ₂Sq_eval_eq_sq hy, hd]; ring)
  refine ⟨x, y, hns, hyne, ?_⟩
  have hmul := addX_self_mul_Ψ₂Sq_eval hy hyne
  rw [hx] at hmul
  exact mul_right_cancel₀ hne hmul

/-! ## Surjectivity of multiplication by `2` -/

/-- **Multiplication by `2` is surjective on `E(F̄)`.** Over an algebraically closed field of
characteristic `≠ 2`, every point of an elliptic curve is twice another point. -/
theorem exists_nsmul_two_eq [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) (Q : W.Point) :
    ∃ P : W.Point, 2 • P = Q := by
  rcases Q with _ | ⟨x₀, y₀, hQ⟩
  · exact ⟨0, smul_zero 2⟩
  · obtain ⟨x, y, hns, hyne, hX⟩ := exists_addX_self_eq (W := W) h2 x₀
    have hdouble : (2 : ℕ) • Point.some x y hns
        = Point.some _ _ (nonsingular_add hns hns fun hxy => hyne hxy.right) := by
      rw [two_nsmul]
      exact Point.add_self_of_Y_ne hyne
    rcases (Point.X_eq_iff (h₂ := hQ)).mp hX with h | h
    · exact ⟨Point.some x y hns, by rw [hdouble, h]⟩
    · refine ⟨-Point.some x y hns, ?_⟩
      rw [smul_neg, hdouble, h, neg_neg]

/-- **Multiplication by `2` is surjective on `E(F̄)`**, stated as `Function.Surjective`. -/
theorem nsmul_two_surjective [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) :
    Function.Surjective fun P : W.Point => (2 : ℕ) • P :=
  exists_nsmul_two_eq h2

end WeierstrassCurve.Affine
