/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.TranslationPlaceAtInfinity
import EllipticCurves.Torsion.TwoTorsion

/-!
# The divisor telescoping at `n = 2`: `f_T · (τ_T∗ f_T)` is a nonzero constant

The first of the two products in Silverman *AEC* III.8.1(b) — the proof that the Weil pairing is
alternating — is a telescoping of divisors over `⟨T⟩`.  At `n = 2` it has two terms, and this file
proves it.

For a `2`-torsion point `T = (x₂, y₂)` and the principal function `f_T` with
`div f_T = 2(T) − 2(O)`, translation by `T` swaps the two points in that divisor, so

```
div (τ_T∗ f_T) = 2(O) − 2(T) = −div f_T,    hence    div (f_T · τ_T∗ f_T) = 0
```

and a function with trivial projective divisor is a nonzero constant.

## Main results

* `WeierstrassCurve.Affine.mapProjPoint_translateAlgEquiv_none_of_negY` — for a point fixed by
  negation, `τ_T` sends the point at infinity to the closed point of `T` itself (rather than of
  `−T`), so together with the merged `mapProjPoint_translateAlgEquiv_pointClosedPoint` it
  **transposes** the two;
* `WeierstrassCurve.Affine.divisorProj_translateEndo_eq_neg` — hence
  `div (τ_T∗ f) = −div f` for any `f` whose divisor is `n(T) − n(O)`, for any `n : ℤ`;
* **`WeierstrassCurve.Affine.exists_mul_translateEndo_eq_algebraMap`** — the telescoping itself:
  for a `2`-torsion point there is `f_T` with `div f_T = 2(T) − 2(O)` and
  `f_T · τ_T∗ f_T = algebraMap F _ c` for some `c ≠ 0`.

## This half is ungated

It needs neither `#418` (`div g_T = [n]∗(T)`), nor `[IsAlgClosed F]`, nor `[2]∗`, nor Ward.  Every
input is merged:

| what | where |
| --- | --- |
| `div f_T = n(T) − n(O)` | `divisorProj_eq_single_sub_single_of_torsion`, `ProjectiveDivisor` |
| `−T = T` for `2`-torsion | `mem_torsion_two_some_iff`, `Torsion/TwoTorsion` |
| transport of the divisor | `divisorProj_translateEndo`, `PlaceOrder.lean` |
| `τ_T : O ↦ (−T)` | `mapProjPoint_translateAlgEquiv_none`, `TranslationPlaceAtInfinity.lean` |
| `τ_T : (T) ↦ O` | `mapProjPoint_translateAlgEquiv_pointClosedPoint`, same file |
| trivial divisor ⟹ constant | `divisorProj_eq_zero_iff`, `ProjectiveDivisor.lean` |

`2`-torsion enters in exactly one place, through `−T = T`: it is what turns the permutation from a
`2`-cycle-plus-unknown into a genuine transposition of the support of `div f_T`, and hence what
makes a two-term telescoping close.  For general `n` the same statement is a product over all of
`⟨T⟩`.  At `n = 3` that is the merged `WeilPairingTelescopeThree`, and it needs **no**
`τ_O`-tolerant translation wrapper: the `i = 0` factor is `f_T` itself and the remaining two
translate by the affine points `T` and `−T`.  A *uniform* statement indexed by `Finset.range n`
would want `translatePointEndo` to name the `i = 0` factor, and genuinely needs it once `T` is
allowed order strictly less than `n`; but the `[i]P = O` obstruction that
`TranslationPointEndomorphism` is written for belongs to the *second* product of III.8.1(b), not to
this one.

## Why it is projective

The affine `divisor W` does **not** transport under `translateEndo`: `τ_T` moves the point at
infinity into the affine chart.  That is the affine-chart caveat of `#409` and the reason `#658`
was done on `ProjPoint W`.  Everything below is `divisorProj`.

## What is *not* here

* `[2]∗`, `mulByTwoEndo`, `g_T`, `#418` — none of them occurs in any statement below.
* `[IsAlgClosed F]`.  Deliberately absent: this half is true over any field, and the hypothesis
  belongs in the assembly, where it is used once to produce a point `P` with `[2]P = T`.
* General `n`, the alternating property itself, antisymmetry.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(b), first product.
-/

open Polynomial IsDedekindDomain

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]
  [IsDedekindDomain W.CoordinateRing] {x₂ y₂ : F}

/-! ### A point fixed by negation -/

omit [W.IsElliptic] [IsDedekindDomain W.CoordinateRing] in
/-- For a point fixed by negation, the closed point of `−T` *is* the closed point of `T`: the two
defining ideals `⟨X − x₂, Y − negY x₂ y₂⟩` and `⟨X − x₂, Y − y₂⟩` are literally the same. -/
lemma pointClosedPoint_equation_neg (h₂ : W.Equation x₂ y₂) (hneg : W.negY x₂ y₂ = y₂) :
    pointClosedPoint ((W.equation_neg x₂ y₂).mpr h₂) = pointClosedPoint h₂ := by
  refine HeightOneSpectrum.ext ?_
  simp only [pointClosedPoint_asIdeal, hneg]

/-- **Translation by a point fixed by negation transposes `O` and the closed point of `T`.**  The
merged `mapProjPoint_translateAlgEquiv_none` sends the point at infinity to the closed point of
`−T`; when `−T = T` that is the closed point of `T`, which the merged
`mapProjPoint_translateAlgEquiv_pointClosedPoint` sends back to the point at infinity. -/
lemma mapProjPoint_translateAlgEquiv_none_of_negY (h₂ : W.Equation x₂ y₂)
    (hneg : W.negY x₂ y₂ = y₂) :
    mapProjPoint W (translateAlgEquiv h₂) none = some (pointClosedPoint h₂) := by
  rw [mapProjPoint_translateAlgEquiv_none h₂, pointClosedPoint_equation_neg h₂ hneg]

/-! ### The transported divisor -/

/-- **`div (τ_T∗ f) = −div f`** whenever `div f = n(T) − n(O)` and `T` is fixed by negation.

The permutation transposes the two points of the support, so the two coefficients `n` and `−n` are
exchanged.  Stated for an arbitrary `n : ℤ`; `n = 2` is the case the telescoping uses. -/
theorem divisorProj_translateEndo_eq_neg (h₂ : W.Equation x₂ y₂) (hneg : W.negY x₂ y₂ = y₂)
    {f : W.FunctionField} (hf : f ≠ 0) {n : ℤ}
    (hdiv : divisorProj W f
      = Finsupp.single (some (pointClosedPoint h₂)) n - Finsupp.single (none : ProjPoint W) n) :
    divisorProj W (translateEndo h₂ f) = -divisorProj W f := by
  classical
  rw [divisorProj_translateEndo h₂ hf, hdiv, Finsupp.mapDomain_sub, Finsupp.mapDomain_single,
    Finsupp.mapDomain_single, mapProjPoint_translateAlgEquiv_pointClosedPoint h₂,
    mapProjPoint_translateAlgEquiv_none_of_negY h₂ hneg]
  abel

/-! ### The telescoping -/

/-- **The two-term telescoping.**  For a `2`-torsion point `T` there is a function `f_T` with
`div f_T = 2(T) − 2(O)` whose product with its own translate by `T` is a nonzero constant.

This is the first of the two products of Silverman III.8.1(b), at `n = 2`.  It carries no hypothesis
beyond `T` being an affine `2`-torsion point: no `#418`, no algebraically closed base field. -/
theorem exists_mul_translateEndo_eq_algebraMap [DecidableEq F] (h : W.Nonsingular x₂ y₂)
    (hP : Point.some x₂ y₂ h ∈ W.torsion 2) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (2 : ℤ)
        - Finsupp.single (none : ProjPoint W) (2 : ℤ) ∧
      ∃ c : F, c ≠ 0 ∧ f * translateEndo h.left f = algebraMap F W.FunctionField c := by
  have hneg : W.negY x₂ y₂ = y₂ := by
    have hy := (mem_torsion_two_some_iff h).mp hP
    rw [negY]
    linear_combination -hy
  obtain ⟨f, hf, hdiv⟩ := divisorProj_eq_single_sub_single_of_torsion h hP
  refine ⟨f, hf, hdiv, ?_⟩
  have hτ : translateEndo h.left f ≠ 0 :=
    fun hz => hf ((translateEndo h.left).injective (by rw [hz, map_zero]))
  refine (divisorProj_eq_zero_iff (mul_ne_zero hf hτ)).mp ?_
  rw [divisorProj_mul hf hτ, divisorProj_translateEndo_eq_neg h.left hneg hf hdiv, add_neg_cancel]

/-! ### Non-vacuity

The telescoping is stated for an affine `2`-torsion point, so it is worth exhibiting a curve
carrying such a point with every instance discharged.  `y² = x³ - x` over `ℚ` has discriminant `64`
and `(0, 0)` is `2`-torsion on it.  ⚠️ This paragraph used to give a second reason — *"the whole
file is conditional on `[IsDedekindDomain W.CoordinateRing]`"* — and that reason was already
false when it was written: `[IsDedekindDomain W.CoordinateRing]` is a binder in this file's
variable block, so `#check` shows it, but it is a **global instance** for `[W.IsElliptic]` over an
**arbitrary** field (`CoordinateRingNormalGeneral`'s `instIsDedekindDomain`, `#476`/`#479`,
merged four days earlier), not a condition on the curve.  The certificate is worth having for the
`2`-torsion point; it certifies nothing about that instance. -/

section Nonvacuity

/-! The certificate curve `y² = x³ − x` is the shared `EllipticCurves.Fixture.y2EqX3SubX`, whose
single `[CharZero F]` instance also supplies `IsElliptic` here. -/

open EllipticCurves.Fixture

/-- `(0, 0)` is a nonsingular point of `y² = x³ - x`. -/
private lemma exampleNonsingular : (y2EqX3SubX ℚ).Nonsingular 0 0 := by
  rw [nonsingular_iff]
  refine ⟨?_, Or.inl ?_⟩ <;> norm_num [y2EqX3SubX]

private lemma exampleTorsion :
    Point.some (0 : ℚ) 0 exampleNonsingular ∈ (y2EqX3SubX ℚ).torsion 2 := by
  rw [mem_torsion_two_some_iff]
  norm_num [y2EqX3SubX]

example : ∃ f : (y2EqX3SubX ℚ).FunctionField, f ≠ 0 ∧
    divisorProj (y2EqX3SubX ℚ) f
      = Finsupp.single (some (pointClosedPoint exampleNonsingular.left)) (2 : ℤ)
        - Finsupp.single (none : ProjPoint (y2EqX3SubX ℚ)) (2 : ℤ) ∧
    ∃ c : ℚ, c ≠ 0 ∧ f * translateEndo exampleNonsingular.left f
      = algebraMap ℚ (y2EqX3SubX ℚ).FunctionField c :=
  exists_mul_translateEndo_eq_algebraMap exampleNonsingular exampleTorsion

end Nonvacuity

end WeierstrassCurve.Affine
