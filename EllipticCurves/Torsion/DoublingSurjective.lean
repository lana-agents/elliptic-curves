/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.DivisionPolynomial.Coprime
import EllipticCurves.Torsion.NsmulSurjective

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

⚠️ **Those two inputs are the whole of what is `n`-specific here, and the argument that consumes
them is not in this file.** `EllipticCurves.Torsion.NsmulSurjective` runs it once at general `n`:
the degree count on `Φₙ - C x₀ · ΨSqₙ`, the root extraction over `F̄`, the point above the root and
the absorption of the sign ambiguity `nP = ±Q`. This file packages the two inputs as
`hasXCoordFormula_two` and `eval_Φ_two_ne_zero_of_root_ΨSq`, and `exists_nsmul_two_eq` is the
resulting one-line instance of `exists_nsmul_eq_of_hasXCoordFormula`.

No hypothesis on `(3 : F)` is used anywhere.

## Main statements

* `WeierstrassCurve.Affine.eval_Φ_two_ne_zero_of_root_ΨSq`: `Φ₂` and `Ψ₂Sq` have no common root —
  input (2) of the engine at `n = 2`.
* `WeierstrassCurve.Affine.addX_self_mul_Ψ₂Sq_eval`: the doubling formula `x(2P) · Ψ₂Sq(x) = Φ₂(x)`.
* `WeierstrassCurve.Affine.hasXCoordFormula_two`: that formula in the form the engine consumes —
  input (1) at `n = 2`.
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

/-! ## Input (2): `Φ₂` and `Ψ₂Sq` have no common root

⚠️ The degree count and the root extraction that used to stand here are `n`-independent and are now
`natDegree_Φ_sub_C_mul_ΨSq` and `exists_eval_Φ_eq` in
`EllipticCurves.Torsion.NsmulSurjective`. -/

/-- **`Φ₂` and `Ψ₂Sq` have no common root.** A common root would be a root of
`Ψ₃ = X·Ψ₂Sq − Φ₂`, and a root of `Ψ₃` is never a root of `Ψ₂Sq`
(`Ψ₂Sq_eval_ne_zero_of_root_Ψ₃`). **No resultant computation and no identity of the form
`A · Φ₂ + B · Ψ₂Sq = Δ` is needed.**

This is the `hroot` hypothesis of `exists_nsmul_eq_of_hasXCoordFormula` at `n = 2`. -/
theorem eval_Φ_two_ne_zero_of_root_ΨSq [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) (x : F)
    (hx : (W.ΨSq 2).eval x = 0) : (W.Φ 2).eval x ≠ 0 := by
  rw [ΨSq_two] at hx
  intro h0
  exact Ψ₂Sq_eval_ne_zero_of_root_Ψ₃ h2 (by rw [Ψ₃_eval_eq_sub, hx, h0]; ring) hx

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
  obtain ⟨x, hx⟩ := exists_eval_Φ_eq (W := W) (n := 2) (by norm_num) x₀
  simp only [Nat.cast_ofNat, ΨSq_two] at hx
  have hne : W.Ψ₂Sq.eval x ≠ 0 := fun h0 =>
    eval_Φ_two_ne_zero_of_root_ΨSq h2 x (by rw [ΨSq_two]; exact h0) (by rw [hx, h0, mul_zero])
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

/-! ## Input (1): the coordinate formula in the form the engine consumes -/

/-- **The coordinate formula at `n = 2`.** A point at which `Ψ₂Sq` does not vanish is not fixed by
negation, so `2 • P` is the tangent sum, whose `x`-coordinate is `Φ₂(x)/Ψ₂Sq(x)` by
`addX_self_mul_Ψ₂Sq_eval`. -/
theorem hasXCoordFormula_two : HasXCoordFormula W 2 := by
  intro x y h hne
  simp only [Nat.cast_ofNat] at hne ⊢
  rw [ΨSq_two] at hne
  have hyeq : W.Equation x y := h.1
  have hyne : y ≠ W.negY x y := by
    intro hcon
    have hd : 2 * y + W.a₁ * x + W.a₃ = 0 := by
      rw [negY] at hcon
      linear_combination hcon
    exact hne (by rw [Ψ₂Sq_eval_eq_sq hyeq, hd]; ring)
  have hX : W.addX x x (W.slope x x y y) = (W.Φ 2).eval x / (W.ΨSq 2).eval x := by
    rw [ΨSq_two, eq_div_iff hne]
    exact addX_self_mul_Ψ₂Sq_eval hyeq hyne
  have hns₂ : W.Nonsingular ((W.Φ 2).eval x / (W.ΨSq 2).eval x)
      (W.addY x x y (W.slope x x y y)) := by
    rw [← hX]
    exact nonsingular_add h h fun hxy => hyne hxy.right
  refine ⟨W.addY x x y (W.slope x x y y), hns₂, ?_⟩
  rw [two_nsmul, Point.add_self_of_Y_ne hyne]
  simp only [Point.some.injEq, and_true]
  exact hX

/-! ## Surjectivity of multiplication by `2` -/

/-- **Multiplication by `2` is surjective on `E(F̄)`.** Over an algebraically closed field of
characteristic `≠ 2`, every point of an elliptic curve is twice another point.

The two inputs above, fed to `exists_nsmul_eq_of_hasXCoordFormula`. -/
theorem exists_nsmul_two_eq [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) (Q : W.Point) :
    ∃ P : W.Point, 2 • P = Q :=
  exists_nsmul_eq_of_hasXCoordFormula h2 (by norm_num)
    (by simp only [Nat.cast_ofNat]; exact eval_Φ_two_ne_zero_of_root_ΨSq h2)
    hasXCoordFormula_two Q

/-- **Multiplication by `2` is surjective on `E(F̄)`**, stated as `Function.Surjective`. -/
theorem nsmul_two_surjective [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) :
    Function.Surjective fun P : W.Point => (2 : ℕ) • P :=
  exists_nsmul_two_eq h2

end WeierstrassCurve.Affine
