/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.ThreeTorsion
import EllipticCurves.Torsion.TwoTorsion
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# The structure of the `3`-torsion subgroup `E[3]`

`EllipticCurves.Torsion.ThreeTorsion` describes `E[3]` as the points lying above the roots of the
`3`-division polynomial `Ψ₃` and deduces `Finite (W.torsion 3)` and `#E[3] ≤ 9` over an arbitrary
field of characteristic `≠ 3`.  This file sharpens that bound to an equality and identifies the
group: for an elliptic curve `W : Affine F` over an **algebraically closed** field `F` of
characteristic `≠ 2` and `≠ 3`,

```
Nat.card (W.torsion 3) = 9        and        W.torsion 3 ≃+ ZMod 3 × ZMod 3.
```

This is the `n = 3` instance of the structure theorem `E[n] ≅ (ℤ/nℤ)²`
(Silverman, *AEC*, III.6, Corollary 6.4), the analogue for `n = 3` of the `n = 2` computation in
`EllipticCurves.Torsion.TwoTorsion`.  Like those files it is **independent of the elliptic-net
recurrence and of the multiplication-by-`n` coordinate formula `x(nP) = Φₙ(x)/ΨSqₙ(x)`**.

## The two missing ingredients

Over an arbitrary field the description of `E[3]` in `ThreeTorsion` leaves two gaps, both closed
here.

**1. Each root of `Ψ₃` really does carry two `3`-torsion points.**  The `⇐` direction of
`mem_torsion_three_some_iff` carries the side condition `y ≠ W.negY x y`.  It is automatic:
writing `d = 2y + a₁x + a₃` and `n = 3x² + 2a₂x + a₄ - a₁y` for the values of `∂W/∂Y` and `-∂W/∂X`,
the doubling defect `Ψ₃_eval_eq_neg` says `n² + a₁nd - (a₂ + 3x)d² = -Ψ₃(x)`, so at a root of `Ψ₃`
with `d = 0` one gets `n = 0` too, and both partial derivatives of the Weierstrass polynomial would
vanish (`Y_ne_negY_of_Ψ₃_eval_eq_zero`).  Hence `Ψ₂Sq.eval x = d² ≠ 0`, the Weierstrass equation is
a *separable* quadratic in `y`, and over an algebraically closed field of characteristic `≠ 2` it
has exactly two roots (`card_setOf_equation_eq_two`).

**2. `Ψ₃` is separable.**  Its formal derivative is `3Ψ₂Sq` (`derivative_Ψ₃`), so a repeated root
of `Ψ₃` would be a common root of `Ψ₃` and `Ψ₂Sq` — excluded by the previous paragraph.  As `Ψ₃` has
degree `4` away from characteristic `3`, over an algebraically closed field it has exactly four
distinct roots (`card_roots_Ψ₃`).  No quartic discriminant is needed.

Combining, `E[3]` is the point at infinity together with two points above each of four roots, so
`#E[3] = 1 + 2 · 4 = 9`, and the group structure follows from the classification core
`AddCommGroup.equiv_zmod_sq_of_card_sq` of `EllipticCurves.Torsion.AbelianStructure`.  The rank
hypothesis of that core at the prime `2` is *not* automatic here (unlike in the `n = 2` case): it
uses instead that an element killed by both `2` and `3` is killed by `1`.

## Main definitions

* `WeierstrassCurve.Affine.torsionThreeOfPair`: the `3`-torsion point attached to a root of `Ψ₃`
  together with a `y`-coordinate above it, with `none` sent to the point at infinity.
* `WeierstrassCurve.Affine.torsionThreeEquiv`: the bijection
  `E[3] ≃ Option ((x : {x // W.Ψ₃.eval x = 0}) × {y // W.Equation x y})`.

## Main statements

* `WeierstrassCurve.Affine.Y_ne_negY_of_Ψ₃_eval_eq_zero`: above a root of `Ψ₃` no point of `W` is
  fixed by negation.
* `WeierstrassCurve.Affine.derivative_Ψ₃`: `Ψ₃' = 3 · Ψ₂Sq`.
* `WeierstrassCurve.Affine.exists_equation_of_isSquare`: a point of `W` lies above `x` as soon as
  `Ψ₂Sq.eval x` is a square, over any field of characteristic `≠ 2`;
  `WeierstrassCurve.Affine.exists_equation` is the algebraically closed case.
* `WeierstrassCurve.Affine.card_roots_Ψ₃`: `Ψ₃` has exactly four roots over an algebraically closed
  field of characteristic `≠ 2, 3`.
* `WeierstrassCurve.Affine.card_torsion_three`: `#E[3] = 9`.
* `WeierstrassCurve.Affine.nonempty_torsionThree_addEquiv`: `E[3] ≃+ ZMod 3 × ZMod 3`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2 (the `3`-torsion points as
  the inflection points of the cubic) and III.6, Corollary 6.4.
-/

open Polynomial

open scoped AddSubgroup

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-! ## No `3`-torsion `x`-coordinate is fixed by negation -/

/-- The value of the `2`-division polynomial `Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆`. -/
lemma Ψ₂Sq_eval (x : F) :
    W.Ψ₂Sq.eval x = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  simp only [Ψ₂Sq, eval_add, eval_mul, eval_pow, eval_C, eval_X]

/-- **Above a root of `Ψ₃` no point of `W` is fixed by negation.**  If `2y + a₁x + a₃` vanished at a
point above a root of `Ψ₃`, the doubling defect `Ψ₃_eval_eq_neg` would force
`3x² + 2a₂x + a₄ - a₁y = 0` as well, so both partial derivatives of the Weierstrass polynomial would
vanish, contradicting nonsingularity. -/
lemma Y_ne_negY_of_Ψ₃_eval_eq_zero {x y : F} (h : W.Nonsingular x y) (hx : W.Ψ₃.eval x = 0) :
    y ≠ W.negY x y := by
  intro hy
  have hd : 2 * y + W.a₁ * x + W.a₃ = 0 := by
    rw [negY] at hy
    linear_combination hy
  have key := Ψ₃_eval_eq_neg h.1
  rw [hx, hd, neg_zero] at key
  have hn : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination key)
  rcases h.2 with hX | hY
  · exact hX (by rw [evalEval_polynomialX]; linear_combination -hn)
  · exact hY (by rw [evalEval_polynomialY]; exact hd)

/-- A root of `Ψ₃` is never a root of `Ψ₂Sq`: the `2`- and `3`-torsion `x`-coordinates are
disjoint. -/
lemma Ψ₂Sq_eval_ne_zero_of_Ψ₃_eval_eq_zero {x y : F} (h : W.Nonsingular x y)
    (hx : W.Ψ₃.eval x = 0) : W.Ψ₂Sq.eval x ≠ 0 := by
  rw [Ψ₂Sq_eval_eq_sq h.1]
  exact pow_ne_zero 2 (two_mul_add_ne_zero_of_Y_ne (Y_ne_negY_of_Ψ₃_eval_eq_zero h hx))

/-- **The side-condition-free membership criterion.**  An affine point of an elliptic curve is
`3`-torsion exactly when its `x`-coordinate is a root of `Ψ₃`; the hypothesis `y ≠ W.negY x y` of
`mem_torsion_three_some_iff` is automatic on both sides. -/
lemma mem_torsion_three_some_iff' [DecidableEq F] {x y : F} {h : W.Nonsingular x y} :
    Point.some x y h ∈ W.torsion 3 ↔ W.Ψ₃.eval x = 0 :=
  ⟨Ψ₃_eval_eq_zero_of_mem_torsion_three,
    fun hx => (mem_torsion_three_some_iff (Y_ne_negY_of_Ψ₃_eval_eq_zero h hx)).mpr hx⟩

/-! ## The fibres of the `x`-coordinate map -/

/-- Away from characteristic `2`, the Weierstrass equation at `(x, y)` says exactly that the
`2`-division value `2y + a₁x + a₃` is a square root of `Ψ₂Sq.eval x`. -/
lemma equation_iff_sq (h2 : (2 : F) ≠ 0) (x y : F) :
    W.Equation x y ↔ (2 * y + W.a₁ * x + W.a₃) ^ 2 = W.Ψ₂Sq.eval x := by
  refine ⟨fun h => (Ψ₂Sq_eval_eq_sq h).symm, fun h => ?_⟩
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  rw [equation_iff']
  refine mul_left_cancel₀ h4 ?_
  rw [mul_zero, Ψ₂Sq_eval] at *
  simp only [b₂, b₄, b₆] at h
  linear_combination h

/-- **Exactly two points of `W` lie above a value of `x` which is not a root of `Ψ₂Sq`**, over an
algebraically closed field of characteristic `≠ 2`: the two square roots of `Ψ₂Sq.eval x` give the
two solutions `y` of the (quadratic) Weierstrass equation. -/
lemma card_setOf_equation_eq_two [IsAlgClosed F] (h2 : (2 : F) ≠ 0) {x : F}
    (hx : W.Ψ₂Sq.eval x ≠ 0) : Nat.card {y : F // W.Equation x y} = 2 := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (W.Ψ₂Sq.eval x) (n := 2) two_pos
  have hs0 : s ≠ 0 := fun h => hx (by rw [← hs, h]; ring)
  have hmem : ∀ y : F, W.Equation x y ↔
      y = (s - W.a₁ * x - W.a₃) / 2 ∨ y = (-s - W.a₁ * x - W.a₃) / 2 := by
    intro y
    rw [equation_iff_sq h2, ← hs]
    constructor
    · intro h
      have h' : (2 * y + W.a₁ * x + W.a₃ - s) * (2 * y + W.a₁ * x + W.a₃ + s) = 0 := by
        linear_combination h
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact Or.inl (by rw [eq_div_iff h2]; linear_combination h'')
      · exact Or.inr (by rw [eq_div_iff h2]; linear_combination h'')
    · rintro (rfl | rfl) <;> field_simp <;> ring
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hne : (s - W.a₁ * x - W.a₃) / 2 ≠ (-s - W.a₁ * x - W.a₃) / 2 := by
    intro h
    rw [div_eq_div_iff h2 h2] at h
    exact hs0 ((mul_eq_zero.mp (show (4 : F) * s = 0 by linear_combination h)).resolve_left h4)
  have hset : {y : F | W.Equation x y}
      = {(s - W.a₁ * x - W.a₃) / 2, (-s - W.a₁ * x - W.a₃) / 2} := by
    ext y
    simpa using hmem y
  have hcard : Nat.card {y : F // W.Equation x y} = ({y : F | W.Equation x y}).ncard :=
    Nat.card_coe_set_eq _
  rw [hcard, hset, Set.ncard_pair hne]

/-- **A point above `x` exists as soon as `Ψ₂Sq.eval x` is a square**, over any field of
characteristic `≠ 2`.

Away from characteristic `2` the Weierstrass equation at `x` is a quadratic in `y` with
discriminant `Ψ₂Sq.eval x` (`equation_iff_sq`), so a square root `s` of that value produces the
point `y = (s - a₁x - a₃)/2` by the quadratic formula.  ⚠️ This is the **only** thing
`exists_equation` below ever used its algebraic closure for.

⚠️ The hypothesis is `IsSquare`, not `∃ s, s ^ 2 = _`.  `IsSquare a` unfolds to `∃ r, a = r * r`,
which is what `equation_iff_sq` wants after a single rewrite and what a caller over a field such as
`ℚ` discharges by exhibiting the root; the `^ 2` form would cost a `sq` rewrite at every call site.

⚠️ `card_setOf_equation_eq_two` above has the same closure use and is deliberately **not**
generalised alongside this: it is a count rather than an existence, so its finite-level form would
need the square to be nonzero as well, and no consumer in this tree wants that statement. -/
lemma exists_equation_of_isSquare (h2 : (2 : F) ≠ 0) {x : F}
    (hsq : IsSquare (W.Ψ₂Sq.eval x)) : ∃ y : F, W.Equation x y := by
  obtain ⟨s, hs⟩ := hsq
  refine ⟨(s - W.a₁ * x - W.a₃) / 2, ?_⟩
  rw [equation_iff_sq h2, hs]
  field_simp
  ring

/-- Over an algebraically closed field of characteristic `≠ 2` every value of `x` is the
`x`-coordinate of a point of `W`: the Weierstrass equation is a quadratic in `y` whose discriminant
`Ψ₂Sq.eval x` always has a square root.

The squareness hypothesis of `exists_equation_of_isSquare`, discharged by
`IsAlgClosed.exists_pow_nat_eq`. -/
lemma exists_equation [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (x : F) : ∃ y : F, W.Equation x y :=
  exists_equation_of_isSquare h2
    (by obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (W.Ψ₂Sq.eval x) (n := 2) two_pos
        exact ⟨s, by rw [← hs]; ring⟩)

/-- A root of `Ψ₃` is never a root of `Ψ₂Sq`, stated without reference to a point above it. -/
lemma Ψ₂Sq_eval_ne_zero_of_root_Ψ₃ [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) {x : F}
    (hx : W.Ψ₃.eval x = 0) : W.Ψ₂Sq.eval x ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_equation h2 x
  exact Ψ₂Sq_eval_ne_zero_of_Ψ₃_eval_eq_zero (equation_iff_nonsingular.mp hy) hx

/-! ## Separability of the `3`-division polynomial -/

/-- The formal derivative of `Ψ₃` is `3 · Ψ₂Sq`. -/
lemma derivative_Ψ₃ : derivative W.Ψ₃ = 3 * W.Ψ₂Sq := by
  simp only [Ψ₃, Ψ₂Sq, derivative_add, derivative_mul, derivative_pow, derivative_X,
    derivative_C, derivative_ofNat, C_mul, C_ofNat, Nat.cast_ofNat]
  ring

variable (W) in
/-- The roots of `Ψ₃`, as a subtype, are exactly the members of its root finset. -/
def rootsEquivΨ₃ [DecidableEq F] (h3 : (3 : F) ≠ 0) :
    {x : F // W.Ψ₃.eval x = 0} ≃ {x : F // x ∈ W.Ψ₃.roots.toFinset} :=
  Equiv.subtypeEquivRight fun x => by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (W.Ψ₃_ne_zero h3)]
    exact Iff.rfl

/-- **`Ψ₃` is separable.**  Its derivative is `3Ψ₂Sq`, and a root of `Ψ₃` is never a root of `Ψ₂Sq`,
so `Ψ₃` has no repeated roots.  In particular no quartic discriminant is needed. -/
lemma nodup_roots_Ψ₃ [W.IsElliptic] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    W.Ψ₃.roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro r
  rw [count_roots]
  by_contra hcount
  rw [not_le] at hcount
  have hroot : W.Ψ₃.eval r = 0 := by
    have hpos : 0 < W.Ψ₃.rootMultiplicity r := lt_of_lt_of_le Nat.zero_lt_one hcount.le
    exact (rootMultiplicity_pos (W.Ψ₃_ne_zero h3)).mp hpos
  have hder : (derivative W.Ψ₃).IsRoot r := by
    simpa using isRoot_iterate_derivative_of_lt_rootMultiplicity (n := 1) hcount
  rw [derivative_Ψ₃, IsRoot, eval_mul, eval_ofNat, mul_eq_zero] at hder
  have hΨ₂ : W.Ψ₂Sq.eval r = 0 := hder.resolve_left h3
  have hy : W.Equation r (W.twoTorsionY r) := equation_twoTorsionY h2 hΨ₂
  exact Ψ₂Sq_eval_ne_zero_of_Ψ₃_eval_eq_zero (equation_iff_nonsingular.mp hy) hroot hΨ₂

/-- **The `3`-division quartic has exactly four roots** over an algebraically closed field of
characteristic `≠ 2, 3`. -/
lemma card_roots_Ψ₃ [W.IsElliptic] [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nat.card {x : F // W.Ψ₃.eval x = 0} = 4 := by
  classical
  rw [Nat.card_congr (W.rootsEquivΨ₃ h3), Nat.card_eq_fintype_card, Fintype.card_coe,
    Multiset.toFinset_card_of_nodup (nodup_roots_Ψ₃ h2 h3),
    ← (IsAlgClosed.splits W.Ψ₃).natDegree_eq_card_roots, W.natDegree_Ψ₃ h3]

/-! ## The count and the structure theorem -/

section Count

variable [DecidableEq F] [W.IsElliptic]

/-- The `3`-torsion point attached to a root `x` of `Ψ₃` together with a `y`-coordinate above it,
with `none` sent to the point at infinity. -/
def torsionThreeOfPair :
    Option ((x : {x : F // W.Ψ₃.eval x = 0}) × {y : F // W.Equation x.1 y}) → W.torsion 3
  | none => 0
  | some ⟨x, y⟩ => ⟨Point.some x.1 y.1 (equation_iff_nonsingular.mp y.2),
      mem_torsion_three_some_iff'.mpr x.2⟩

lemma torsionThreeOfPair_bijective :
    Function.Bijective (torsionThreeOfPair (W := W)) := by
  constructor
  · rintro (_ | ⟨⟨x₁, hx₁⟩, ⟨y₁, hy₁⟩⟩) (_ | ⟨⟨x₂, hx₂⟩, ⟨y₂, hy₂⟩⟩) hab
    · rfl
    · exact absurd (congrArg Subtype.val hab).symm (Point.some_ne_zero _)
    · exact absurd (congrArg Subtype.val hab) (Point.some_ne_zero _)
    · have hxy := congrArg Subtype.val hab
      rw [torsionThreeOfPair, torsionThreeOfPair, Point.some.injEq] at hxy
      obtain ⟨rfl, rfl⟩ := hxy
      rfl
  · rintro ⟨(_ | ⟨x, y, h⟩), hP⟩
    · exact ⟨none, rfl⟩
    · exact ⟨some ⟨⟨x, mem_torsion_three_some_iff'.mp hP⟩, ⟨y, h.1⟩⟩, rfl⟩

/-- **`E[3]` is the point at infinity together with the points above the roots of `Ψ₃`.** -/
noncomputable def torsionThreeEquiv :
    W.torsion 3 ≃ Option ((x : {x : F // W.Ψ₃.eval x = 0}) × {y : F // W.Equation x.1 y}) :=
  (Equiv.ofBijective _ torsionThreeOfPair_bijective).symm

variable [IsAlgClosed F]

/-- **`#E[3] = 9`** for an elliptic curve over an algebraically closed field of characteristic
`≠ 2, 3`: the point at infinity together with the two points above each of the four roots of the
`3`-division quartic. -/
theorem card_torsion_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nat.card (W.torsion 3) = 9 := by
  haveI : Finite {x : F // W.Ψ₃.eval x = 0} :=
    (W.finite_setOf_Ψ₃_root h3).to_subtype
  haveI : Fintype {x : F // W.Ψ₃.eval x = 0} := Fintype.ofFinite _
  haveI : ∀ x : {x : F // W.Ψ₃.eval x = 0}, Finite {y : F // W.Equation x.1 y} :=
    fun x => (W.setOf_equation_finite x.1).to_subtype
  have hfib : ∀ x : {x : F // W.Ψ₃.eval x = 0}, Nat.card {y : F // W.Equation x.1 y} = 2 :=
    fun x => card_setOf_equation_eq_two h2 (Ψ₂Sq_eval_ne_zero_of_root_Ψ₃ h2 x.2)
  have hroots : Fintype.card {x : F // W.Ψ₃.eval x = 0} = 4 := by
    rw [← Nat.card_eq_fintype_card, card_roots_Ψ₃ h2 h3]
  rw [Nat.card_congr torsionThreeEquiv, Finite.card_option, Nat.card_sigma,
    Finset.sum_congr rfl fun x _ => hfib x, Finset.sum_const, Finset.card_univ, hroots]
  norm_num

/-- **The structure theorem for `E[3]`.**  Over an algebraically closed field of characteristic
`≠ 2, 3`, the `3`-torsion subgroup of an elliptic curve is isomorphic to `ℤ/3ℤ × ℤ/3ℤ`.

This is the `n = 3` instance of `E[n] ≅ (ℤ/nℤ)²`, obtained by feeding the count `#E[3] = 9` into
the finite-abelian-group classification core `AddCommGroup.equiv_zmod_sq_of_card_sq`. -/
theorem nonempty_torsionThree_addEquiv (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nonempty (W.torsion 3 ≃+ ZMod 3 × ZMod 3) := by
  haveI := W.finite_torsion_three h3
  have hcard : Nat.card (W.torsion 3) = 3 ^ 2 := by
    rw [card_torsion_three h2 h3]
    norm_num
  refine AddCommGroup.equiv_zmod_sq_of_card_sq three_pos (fun a => nsmul_mem_torsion a) hcard ?_
  intro p hp
  rcases eq_or_ne p 2 with rfl | hp2
  · -- an element of `E[3]` killed by `2` is killed by `3 - 2 = 1`
    have hone : ∀ a : W.torsion 3, (2 : ℕ) • a = 0 → a = 0 := by
      intro a ha
      have h3a : (3 : ℕ) • a = 0 := nsmul_mem_torsion a
      have key : (2 : ℕ) • a + a = (3 : ℕ) • a := by rw [← succ_nsmul]
      rw [ha, zero_add, h3a] at key
      exact key
    have hcard1 : Nat.card {a : W.torsion 3 // (2 : ℕ) • a = 0} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext ((hone a.1 a.2).trans (hone b.1 b.2).symm)⟩,
        ⟨⟨0, by simp⟩⟩⟩
    rw [hcard1]
    norm_num
  · have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    calc Nat.card {a : W.torsion 3 // p • a = 0}
        ≤ Nat.card (W.torsion 3) := Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = 3 ^ 2 := hcard
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2

end Count

end WeierstrassCurve.Affine
