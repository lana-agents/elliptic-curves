/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.AbelianStructure
import EllipticCurves.Torsion.DivisionPolynomialEval
import EllipticCurves.Torsion.Finite
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The `2`-torsion subgroup `E[2]`

For an elliptic curve `W : Affine F` over an **algebraically closed** field `F` of characteristic
`≠ 2`, this file computes the `2`-torsion subgroup completely:

```
Nat.card (W.torsion 2) = 4        and        W.torsion 2 ≃+ ZMod 2 × ZMod 2.
```

This is the `n = 2` instance of the structure theorem `E[n] ≅ (ℤ/nℤ)²`
(Silverman, *AEC*, III.6, Corollary 6.4), and the first actual computation of a torsion group in
this development. Unlike the general case it is **independent of the elliptic-net recurrence and of
the multiplication-by-`n` coordinate formula `x(nP) = Φₙ(x)/ΨSqₙ(x)`**: for `n = 2` everything
reduces to the fact that the Weierstrass equation is quadratic in `y`, together with the
discriminant of a cubic.

## The mechanism

A point `P` is killed by `2` exactly when `P = -P`. For an affine point `P = (x, y)` negation acts
by `y ↦ negY x y = -y - a₁x - a₃`, so

```
2 • P = 0  ↔  2y + a₁x + a₃ = 0  ↔  ψ₂(x, y) = 0.
```

Mathlib's congruence `ψ₂² ≡ Ψ₂Sq (mod W)` — transported to an honest identity at a point of `W` by
`WeierstrassCurve.Affine.ψ_sq_evalEval` — turns this into the pointwise identity

```
W.Ψ₂Sq.eval x = (2y + a₁x + a₃) ^ 2                for every `(x, y)` on `W`,
```

recorded below as `Ψ₂Sq_eval_eq_sq`. Consequently:

* a nonzero `2`-torsion point has an `x`-coordinate which is a root of the cubic `Ψ₂Sq`;
* conversely, if `(2 : F) ≠ 0` and `x` is a root of `Ψ₂Sq`, then the *unique* candidate
  `y = -(a₁x + a₃)/2` (`twoTorsionY`) already satisfies the Weierstrass equation, because the
  displayed identity forces `4 · W.polynomial.evalEval x y = 0`.

So `E[2]` is the point at infinity together with the roots of `Ψ₂Sq` (`torsionTwoEquiv`). Since
`Ψ₂Sq` is Mathlib's `twoTorsionPolynomial`, a cubic with leading coefficient `4` and discriminant
`16Δ`, over an algebraically closed field of characteristic `≠ 2` it has exactly three distinct
roots, whence `#E[2] = 1 + 3 = 4`.

The group structure then follows from the finite-abelian-group classification core
`AddCommGroup.equiv_zmod_sq_of_card_sq` of `EllipticCurves.Torsion.AbelianStructure`.

## Main definitions

* `WeierstrassCurve.Affine.twoTorsionY`: the `y`-coordinate `-(a₁x + a₃)/2` of the unique point of
  `W` above `x` that is fixed by negation.
* `WeierstrassCurve.Affine.torsionTwoOfRoot`: the `2`-torsion point attached to a root of `Ψ₂Sq`,
  with `none` sent to the point at infinity.
* `WeierstrassCurve.Affine.torsionTwoEquiv`: the bijection
  `E[2] ≃ Option {x // W.Ψ₂Sq.eval x = 0}`.

## Main statements

* `WeierstrassCurve.Affine.Ψ₂Sq_eval_eq_sq`: `W.Ψ₂Sq.eval x = (2y + a₁x + a₃)²` at a point of `W`.
* `WeierstrassCurve.Affine.mem_torsion_two_some_iff`: `(x, y) ∈ E[2] ↔ 2y + a₁x + a₃ = 0`.
* `WeierstrassCurve.Affine.card_roots_Ψ₂Sq`: the cubic `Ψ₂Sq` has exactly three roots over an
  algebraically closed field of characteristic `≠ 2`.
* `WeierstrassCurve.Affine.card_torsion_two`: `#E[2] = 4`.
* `WeierstrassCurve.Affine.nonempty_torsionTwo_addEquiv`: `E[2] ≃+ ZMod 2 × ZMod 2`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2 (the description of `E[2]`
  by the roots of the `2`-division polynomial) and III.6, Corollary 6.4.
-/

open Polynomial

open scoped AddSubgroup

namespace WeierstrassCurve.Affine

private lemma four_ne_zero_of_two_ne_zero {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) :
    (4 : F) ≠ 0 := by
  rw [show (4 : F) = 2 * 2 by norm_num]
  exact mul_ne_zero h2 h2

variable {F : Type*} [Field F] {W : Affine F}

/-! ## The `2`-division polynomial at a point -/

/-- The square of the `2`-division polynomial at a point `(x, y)` of `W` is the value at `x` of the
univariate cubic `Ψ₂Sq`: `W.Ψ₂Sq.eval x = (2y + a₁x + a₃)²`.

This is the `n = 2` case of `WeierstrassCurve.Affine.ψ_sq_evalEval`, and it is the sole input to
the description of `E[2]` by the roots of `Ψ₂Sq`. -/
lemma Ψ₂Sq_eval_eq_sq {x y : F} (h : W.Equation x y) :
    W.Ψ₂Sq.eval x = (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
  rw [← ΨSq_two, ← ψ_sq_evalEval h 2, ψ_two_evalEval]

/-- **The converse construction.** Away from characteristic `2`, a root `x` of `Ψ₂Sq` together with
the unique `y` satisfying `2y + a₁x + a₃ = 0` gives a point of `W`: multiplying the Weierstrass
equation by `4` turns it into `(2y + a₁x + a₃)² - W.Ψ₂Sq.eval x = 0`. -/
lemma equation_of_Ψ₂Sq_eval_eq_zero (h2 : (2 : F) ≠ 0) {x y : F}
    (hy : 2 * y + W.a₁ * x + W.a₃ = 0) (hx : W.Ψ₂Sq.eval x = 0) : W.Equation x y := by
  have h4 : (4 : F) ≠ 0 := four_ne_zero_of_two_ne_zero h2
  rw [equation_iff']
  apply mul_left_cancel₀ h4
  rw [mul_zero]
  simp only [Ψ₂Sq, b₂, b₄, b₆, eval_add, eval_mul, eval_pow, eval_C, eval_X] at hx
  linear_combination (2 * y + W.a₁ * x + W.a₃) * hy - hx

variable (W) in
/-- The `y`-coordinate `-(a₁x + a₃)/2` of the unique point of `W` above `x` fixed by negation.

Away from characteristic `2` this is the only possible `y`-coordinate of a `2`-torsion point with
`x`-coordinate `x`. -/
def twoTorsionY (x : F) : F :=
  -(W.a₁ * x + W.a₃) / 2

/-- The defining property of `twoTorsionY`: it is the unique root of `2y + a₁x + a₃`. -/
lemma two_mul_twoTorsionY_add (h2 : (2 : F) ≠ 0) (x : F) :
    2 * W.twoTorsionY x + W.a₁ * x + W.a₃ = 0 := by
  rw [twoTorsionY]
  field_simp
  ring

/-- Above a root of `Ψ₂Sq`, the point `(x, twoTorsionY x)` lies on `W`. -/
lemma equation_twoTorsionY (h2 : (2 : F) ≠ 0) {x : F} (hx : W.Ψ₂Sq.eval x = 0) :
    W.Equation x (W.twoTorsionY x) :=
  equation_of_Ψ₂Sq_eval_eq_zero h2 (two_mul_twoTorsionY_add h2 x) hx

/-- On an elliptic curve every point of the Weierstrass equation is nonsingular, so above a root of
`Ψ₂Sq` the point `(x, twoTorsionY x)` is a genuine point of `W.Point`. -/
lemma nonsingular_twoTorsionY [W.IsElliptic] (h2 : (2 : F) ≠ 0) {x : F}
    (hx : W.Ψ₂Sq.eval x = 0) : W.Nonsingular x (W.twoTorsionY x) :=
  equation_iff_nonsingular.mp (equation_twoTorsionY h2 hx)

/-! ## The roots of the `2`-torsion cubic -/

/-- The leading coefficient of the `2`-torsion cubic is `4`, nonzero away from characteristic `2`.
-/
lemma twoTorsionPolynomial_a_ne_zero (h2 : (2 : F) ≠ 0) : W.twoTorsionPolynomial.a ≠ 0 := by
  rw [twoTorsionPolynomial, show (4 : F) = 2 * 2 by norm_num]
  exact mul_ne_zero h2 h2

variable (W) in
/-- The roots of `Ψ₂Sq`, as a subtype, are exactly the members of its root finset. -/
def rootsEquiv [DecidableEq F] (h2 : (2 : F) ≠ 0) :
    {x : F // W.Ψ₂Sq.eval x = 0} ≃ {x : F // x ∈ W.Ψ₂Sq.roots.toFinset} :=
  Equiv.subtypeEquivRight fun x => by
    rw [Multiset.mem_toFinset,
      Polynomial.mem_roots (W.Ψ₂Sq_ne_zero (four_ne_zero_of_two_ne_zero h2))]
    exact Iff.rfl

/-- Away from characteristic `2` the cubic `Ψ₂Sq` is nonzero, so its root set is finite. -/
lemma finite_roots_Ψ₂Sq (h2 : (2 : F) ≠ 0) : Finite {x : F // W.Ψ₂Sq.eval x = 0} := by
  classical
  exact Finite.of_equiv _ (W.rootsEquiv h2).symm

/-- **The `2`-torsion cubic has exactly three roots** over an algebraically closed field of
characteristic `≠ 2`: it is a cubic with leading coefficient `4` and discriminant `16Δ`, both units
for an elliptic curve away from characteristic `2`. -/
lemma card_roots_Ψ₂Sq [W.IsElliptic] [IsAlgClosed F] (h2 : (2 : F) ≠ 0) :
    Nat.card {x : F // W.Ψ₂Sq.eval x = 0} = 3 := by
  classical
  have ha : W.twoTorsionPolynomial.a ≠ 0 := W.twoTorsionPolynomial_a_ne_zero h2
  have hd : W.twoTorsionPolynomial.discr ≠ 0 :=
    W.twoTorsionPolynomial_discr_ne_zero_of_isElliptic h2.isUnit
  have hsplits : (W.twoTorsionPolynomial.toPoly.map (RingHom.id F)).Splits := by
    rw [Polynomial.map_id]
    exact IsAlgClosed.splits _
  have hcard := Cubic.card_roots_of_discr_ne_zero (φ := RingHom.id F) ha hsplits hd
  have hmap : Cubic.map (RingHom.id F) W.twoTorsionPolynomial = W.twoTorsionPolynomial := rfl
  rw [hmap, Cubic.roots, ← Ψ₂Sq_eq] at hcard
  rw [Nat.card_congr (W.rootsEquiv h2), Nat.card_eq_fintype_card, Fintype.card_coe]
  exact hcard

/-! ## The `2`-torsion subgroup -/

section Torsion

variable [DecidableEq F]

/-- A point is killed by `2` exactly when it is fixed by negation. -/
lemma mem_torsion_two_iff_eq_neg {P : W.Point} : P ∈ W.torsion 2 ↔ P = -P := by
  rw [mem_torsion_iff, two_nsmul, add_eq_zero_iff_eq_neg]

/-- An affine point `(x, y)` is `2`-torsion exactly when the `2`-division polynomial
`ψ₂ = 2y + a₁x + a₃` vanishes at it. -/
lemma mem_torsion_two_some_iff {x y : F} (h : W.Nonsingular x y) :
    Point.some x y h ∈ W.torsion 2 ↔ 2 * y + W.a₁ * x + W.a₃ = 0 := by
  rw [mem_torsion_two_iff_eq_neg, Point.neg_some, Point.some.injEq]
  simp only [negY, true_and]
  constructor <;> intro hy <;> linear_combination hy

/-- The `y`-coordinate of an affine `2`-torsion point is forced: it is `twoTorsionY x`. -/
lemma eq_twoTorsionY_of_mem_torsion_two (h2 : (2 : F) ≠ 0) {x y : F} {h : W.Nonsingular x y}
    (hP : Point.some x y h ∈ W.torsion 2) : y = W.twoTorsionY x := by
  have hy := (mem_torsion_two_some_iff h).mp hP
  rw [twoTorsionY, eq_div_iff h2]
  linear_combination hy

/-- The `x`-coordinate of an affine `2`-torsion point is a root of the cubic `Ψ₂Sq`. -/
lemma Ψ₂Sq_eval_eq_zero_of_mem_torsion_two {x y : F} {h : W.Nonsingular x y}
    (hP : Point.some x y h ∈ W.torsion 2) : W.Ψ₂Sq.eval x = 0 := by
  rw [Ψ₂Sq_eval_eq_sq h.1, (mem_torsion_two_some_iff h).mp hP]
  ring

variable [W.IsElliptic]

/-- The `2`-torsion point attached to a root of `Ψ₂Sq`, with `none` sent to the point at infinity.
-/
def torsionTwoOfRoot (h2 : (2 : F) ≠ 0) :
    Option {x : F // W.Ψ₂Sq.eval x = 0} → W.torsion 2
  | none => 0
  | some x => ⟨Point.some x (W.twoTorsionY x) (nonsingular_twoTorsionY h2 x.2),
      (mem_torsion_two_some_iff _).mpr (two_mul_twoTorsionY_add h2 x)⟩

lemma torsionTwoOfRoot_bijective (h2 : (2 : F) ≠ 0) :
    Function.Bijective (torsionTwoOfRoot (W := W) h2) := by
  constructor
  · rintro (_ | ⟨x₁, hx₁⟩) (_ | ⟨x₂, hx₂⟩) hab
    · rfl
    · exact absurd (congrArg Subtype.val hab).symm (Point.some_ne_zero _)
    · exact absurd (congrArg Subtype.val hab) (Point.some_ne_zero _)
    · have hx := congrArg Subtype.val hab
      rw [torsionTwoOfRoot, torsionTwoOfRoot, Point.some.injEq] at hx
      exact congrArg _ (Subtype.ext hx.1)
  · rintro ⟨(_ | ⟨x, y, h⟩), hP⟩
    · exact ⟨none, rfl⟩
    · exact ⟨some ⟨x, Ψ₂Sq_eval_eq_zero_of_mem_torsion_two hP⟩,
        Subtype.ext (by
          rw [torsionTwoOfRoot]
          simp only [Point.some.injEq]
          exact ⟨trivial, (eq_twoTorsionY_of_mem_torsion_two h2 hP).symm⟩)⟩

/-- **`E[2]` is the point at infinity together with the roots of `Ψ₂Sq`.** -/
noncomputable def torsionTwoEquiv (h2 : (2 : F) ≠ 0) :
    W.torsion 2 ≃ Option {x : F // W.Ψ₂Sq.eval x = 0} :=
  (Equiv.ofBijective _ (torsionTwoOfRoot_bijective h2)).symm

/-- Away from characteristic `2` the `2`-torsion subgroup of an elliptic curve is finite. -/
lemma finite_torsion_two (h2 : (2 : F) ≠ 0) : Finite (W.torsion 2) :=
  haveI := W.finite_roots_Ψ₂Sq h2
  Finite.of_equiv _ (torsionTwoEquiv h2).symm

/-- **`#E[2] = 4`** for an elliptic curve over an algebraically closed field of characteristic
`≠ 2`: the point at infinity together with the three roots of the `2`-torsion cubic. -/
theorem card_torsion_two [IsAlgClosed F] (h2 : (2 : F) ≠ 0) : Nat.card (W.torsion 2) = 4 := by
  haveI := W.finite_roots_Ψ₂Sq h2
  rw [Nat.card_congr (torsionTwoEquiv h2), Finite.card_option, card_roots_Ψ₂Sq h2]

/-- **The structure theorem for `E[2]`.** Over an algebraically closed field of characteristic
`≠ 2`, the `2`-torsion subgroup of an elliptic curve is isomorphic to `ℤ/2ℤ × ℤ/2ℤ`.

This is the `n = 2` instance of `E[n] ≅ (ℤ/nℤ)²`, obtained by feeding the count `#E[2] = 4` into
the finite-abelian-group classification core `AddCommGroup.equiv_zmod_sq_of_card_sq`. -/
theorem nonempty_torsionTwo_addEquiv [IsAlgClosed F] (h2 : (2 : F) ≠ 0) :
    Nonempty (W.torsion 2 ≃+ ZMod 2 × ZMod 2) := by
  haveI := W.finite_torsion_two h2
  have hcard : Nat.card (W.torsion 2) = 2 ^ 2 := by
    rw [card_torsion_two h2]
    norm_num
  refine AddCommGroup.equiv_zmod_sq_of_card_sq two_pos (fun a => nsmul_mem_torsion a) hcard ?_
  intro p hp
  calc Nat.card {a : W.torsion 2 // p • a = 0}
      ≤ Nat.card (W.torsion 2) := Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = 2 ^ 2 := hcard
    _ ≤ p ^ 2 := Nat.pow_le_pow_left hp.two_le 2

end Torsion

end WeierstrassCurve.Affine
