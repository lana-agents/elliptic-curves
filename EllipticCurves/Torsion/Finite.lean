/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.Defs

/-!
# A finiteness engine for point sets with bounded `x`-support

For a Weierstrass curve `W` over a field `F`, the Weierstrass equation `y² + a₁xy + a₃y = x³ + …`
is *quadratic in `y`*, so for each fixed `x` there are at most two points `(x, y)` on the curve:
any two solutions `y₁, y₂` satisfy `y₁ = y₂` or `y₁ = negY x y₂` (Mathlib's
`WeierstrassCurve.Affine.Y_eq_of_X_eq`). Consequently, **any set of affine points whose
`x`-coordinates lie in a finite set is itself finite**.

This is the purely geometric counting infrastructure behind the finiteness of `E[n]` (issue #252,
rung 3 of the `#E[n] ≤ n²` program, parent #246). It is deliberately **independent of the
division-polynomial / elliptic-net recurrence**: it takes the finite `x`-support as a *hypothesis*.
The remaining input — that every nonzero `n`-torsion point has an `x`-coordinate among the
`≤ n² − 1` roots of `W.ΨSq n` — is supplied by the multiplication-by-`n` characterisation (#251)
and, once available, plugs directly into
`WeierstrassCurve.Affine.torsion_finite_of_xCoords` below to conclude `Finite E[n]`.

## Main statements

* `WeierstrassCurve.Affine.setOf_equation_subset_pair`: the `y`-fibre `{y | W.Equation x y}` is
  contained in the two-element set `{y₀, W.negY x y₀}` for any solution `y₀`.
* `WeierstrassCurve.Affine.setOf_equation_finite`: the `y`-fibre over a fixed `x` is finite.
* `WeierstrassCurve.Affine.finite_of_xCoords`: a set of points whose nonzero members have
  `x`-coordinate in a finite set `S` is finite.
* `WeierstrassCurve.Affine.torsion_finite_of_xCoords`,
  `WeierstrassCurve.Affine.finite_torsion_of_xCoords`: the specialisation to `E[n]`, the exact
  interface the `#E[n] ≤ n²` counting (#252) consumes once #251 supplies the finite `x`-support.

## References

Silverman, *The Arithmetic of Elliptic Curves*, III.4 and III.6 Cor 6.4 (the sharp count).
-/

open scoped AddSubgroup

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : Affine F)

/-- The `y`-fibre of the Weierstrass equation over a fixed `x` is contained in the two-element set
`{y₀, W.negY x y₀}` cut out by any single solution `y₀`: the equation is quadratic in `y`, and
`Y_eq_of_X_eq` says any two solutions coincide up to the `negY` involution. -/
lemma setOf_equation_subset_pair {x y₀ : F} (h₀ : W.Equation x y₀) :
    {y : F | W.Equation x y} ⊆ {y₀, W.negY x y₀} := by
  intro y hy
  rcases Y_eq_of_X_eq hy h₀ rfl with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- For each fixed `x`, only finitely many `y` satisfy the Weierstrass equation `W.Equation x y`
(at most two). -/
lemma setOf_equation_finite (x : F) : {y : F | W.Equation x y}.Finite := by
  rcases Set.eq_empty_or_nonempty {y : F | W.Equation x y} with h | ⟨y₀, h₀⟩
  · rw [h]; exact Set.finite_empty
  · exact ((Set.finite_singleton _).insert _).subset
      (W.setOf_equation_subset_pair h₀)

/-- The `y`-fibre over a fixed `x` has at most two elements. -/
lemma setOf_equation_ncard_le_two (x : F) : {y : F | W.Equation x y}.ncard ≤ 2 := by
  rcases Set.eq_empty_or_nonempty {y : F | W.Equation x y} with h | ⟨y₀, h₀⟩
  · rw [h, Set.ncard_empty]; norm_num
  · calc {y : F | W.Equation x y}.ncard
        ≤ ({y₀, W.negY x y₀} : Set F).ncard :=
          Set.ncard_le_ncard (W.setOf_equation_subset_pair h₀) (Set.toFinite _)
      _ ≤ 2 := by
          refine (Set.ncard_insert_le _ _).trans ?_
          rw [Set.ncard_singleton]

/-- The auxiliary "coordinate tag" map: the identity point goes to `none`, and a genuine point
`(x, y)` goes to `some (x, y)`. It is injective, and turns finiteness of a set of points into
finiteness of a set of tags. -/
private def coordTag : W.Point → Option (F × F)
  | 0 => none
  | .some x y _ => some (x, y)

private lemma coordTag_injective : Function.Injective W.coordTag := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h <;>
    simp only [coordTag, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
  · rfl
  · obtain ⟨rfl, rfl⟩ := h; rfl

/-- **Finiteness engine.** A set `A` of affine points on `W` whose *nonzero* members all have
`x`-coordinate in a finite set `S` is itself finite.

This is the geometric heart of the `#E[n] ≤ n²` finiteness argument (#252): the Weierstrass
equation is quadratic in `y`, so each `x ∈ S` supports at most two points, and `A` embeds into the
finite set of such coordinate pairs (plus the identity). -/
theorem finite_of_xCoords {A : Set W.Point} {S : Set F} (hS : S.Finite)
    (hx : ∀ ⦃x y : F⦄ ⦃h : W.Nonsingular x y⦄, (.some x y h : W.Point) ∈ A → x ∈ S) :
    A.Finite := by
  -- The set of coordinate pairs with `x`-coordinate in `S` that lie on the curve.
  set T : Set (F × F) := {p : F × F | p.1 ∈ S ∧ W.Equation p.1 p.2} with hT
  -- `T` is finite: it is the union over `x ∈ S` of the (finite) `y`-fibres.
  have hTfin : T.Finite := by
    apply Set.Finite.subset (hS.biUnion fun x _ => (W.setOf_equation_finite x).image (Prod.mk x))
    rintro ⟨x, y⟩ ⟨hxS, hxy⟩
    exact Set.mem_biUnion hxS ⟨y, hxy, rfl⟩
  -- `A` embeds into `insert none (some '' T)` via the injective coordinate tag.
  refine Set.Finite.of_finite_image (f := W.coordTag) ?_ (W.coordTag_injective.injOn)
  refine ((hTfin.image some).insert none).subset ?_
  rintro _ ⟨(_ | ⟨x, y, h⟩), hP, rfl⟩
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ⟨(x, y), ⟨hx hP, h.left⟩, rfl⟩

variable [DecidableEq F]

/-- Specialisation of `finite_of_xCoords` to the `n`-torsion subgroup `E[n]`: if every nonzero
`n`-torsion point has `x`-coordinate in a finite set `S`, then `E[n]` is finite (as a set of
points). This is the exact interface the `#E[n] ≤ n²` counting (#252) consumes once #251 provides
the finite root set of `W.ΨSq n` as `S`. -/
theorem torsion_finite_of_xCoords {n : ℕ} {S : Set F} (hS : S.Finite)
    (hx : ∀ ⦃x y : F⦄ ⦃h : W.Nonsingular x y⦄,
      (.some x y h : W.Point) ∈ W.torsion n → x ∈ S) :
    (W.torsion n : Set W.Point).Finite :=
  W.finite_of_xCoords hS hx

/-- The subtype form of `torsion_finite_of_xCoords`: `E[n]` is a `Finite` type once its nonzero
points have `x`-coordinates in a finite set. -/
theorem finite_torsion_of_xCoords {n : ℕ} {S : Set F} (hS : S.Finite)
    (hx : ∀ ⦃x y : F⦄ ⦃h : W.Nonsingular x y⦄,
      (.some x y h : W.Point) ∈ W.torsion n → x ∈ S) :
    Finite (W.torsion n) :=
  Set.finite_coe_iff.mpr (W.torsion_finite_of_xCoords hS hx)

end WeierstrassCurve.Affine
