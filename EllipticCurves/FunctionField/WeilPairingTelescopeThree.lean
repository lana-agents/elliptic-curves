/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.TranslationProjAction
import EllipticCurves.FunctionField.TranslationTorsionMap
import EllipticCurves.Torsion.ThreeTorsion

/-!
# The divisor telescoping at `n = 3`: `f_T · (τ_T∗ f_T) · (τ_{−T}∗ f_T)` is a nonzero constant

The first of the two products in Silverman *AEC* III.8.1(d) — the proof that the Weil pairing is
alternating — is a telescoping of divisors over the cyclic subgroup `⟨T⟩`.  At `n = 2` it has two
terms and `EllipticCurves.FunctionField.WeilPairingTelescopeTwo` proves it.  This file is the
`n = 3` case, where it has three.

For a `3`-torsion point `T = (x₃, y₃)` and the principal function `f_T` with
`div f_T = 3(T) − 3(O)`, the three translates of `div f_T` by the elements of `⟨T⟩` cancel in a
cycle rather than in a single transposition:

```
div f_T          = 3(T)  − 3(O)
div (τ_T∗  f_T)  = 3(O)  − 3(−T)
div (τ_{−T}∗ f_T) = 3(−T) − 3(T)
```

so their sum vanishes and the product is a nonzero constant.

## `−T` is the third translation, and it is affine

`⟨T⟩ = {O, T, 2T}`, and `T ⊕ T ⊕ T = O` gives `2T = −T`, whose coordinates are
`(x₃, negY x₃ y₃)`; so the third translation is by an *affine* point and `translateEndo` expresses
it.  The `i = 0` factor is `f_T` itself, so `τ_O` never appears.

⚠️ This is a fact about **this** product only.  The *second* product of III.8.1(d), the one the
assembly runs, is `∏_{i} τ_{[i]P}∗ g_T` for a point `P` with `[3]P = T`, and there `[i]P = O` can
occur for `0 < i < 3`; that product does need the `τ_O`-tolerant wrapper `translatePointEndo`
(`TranslationPointEndomorphism`, `#689`).  Nothing in this file needs it.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.translatePoint_neg_add_neg_of_three_torsion` — the group
  relation `𝒯_{−T} + 𝒯_{−T} = 𝒯_T` over `F(W)`, which is `3T = O` rearranged;
* `WeierstrassCurve.Affine.divisorProj_translateEndo_eq_none_sub_neg` — the second row of the table:
  `div (τ_T∗ f) = n·O − n(−T)` whenever `div f = n(T) − n·O`;
* `WeierstrassCurve.Affine.divisorProj_translateEndo_neg_eq_neg_sub` — the third row:
  `div (τ_{−T}∗ f) = n(−T) − n(T)`, which is where the `3`-torsion hypothesis enters;
* **`WeierstrassCurve.Affine.exists_mul_translateEndo_mul_translateEndo_eq_algebraMap`** — the
  telescoping itself.

Both transported-divisor lemmas are stated for an arbitrary `n : ℤ`, and exposed rather than
inlined, because the assembly wants them separately — the `n = 2` file exposes
`divisorProj_translateEndo_eq_neg` for the same reason.

## This half is ungated

It needs neither `#418` (`div g_T = [n]∗(T)`), nor `[IsAlgClosed F]`, nor `[3]∗`, nor Ward, nor any
characteristic hypothesis.  Every input is merged:

| what | where |
| --- | --- |
| `div f_T = n(T) − n(O)` | `divisorProj_eq_single_sub_single_of_torsion`, `ProjectiveDivisor` |
| transport of the divisor | `divisorProj_translateEndo`, `PlaceOrder.lean` |
| `τ_T : O ↦ (−T)` | `mapProjPoint_translateAlgEquiv_none`, `TranslationPlaceAtInfinity.lean` |
| `τ_T : (T) ↦ O` | `mapProjPoint_translateAlgEquiv_pointClosedPoint`, same file |
| `τ_{−T} : O ↦ (T)` | `mapProjPoint_translateAlgEquiv_neg_none`, `TranslationProjAction.lean` |
| `τ_{−T} : (T) ↦ (−T)` | `mapProjPoint_translateAlgEquiv_pointClosedPoint_affine`, same file |
| `3T = O` over `F(W)` | `translatePoint_add_add_self`, `TranslationTorsionMap.lean` |
| trivial divisor ⟹ constant | `divisorProj_eq_zero_iff`, `ProjectiveDivisor.lean` |

## What is different from `n = 2`

At `n = 2` the point `T` is fixed by negation, so `(−T)` *is* `(T)` and the permutation of the
support of `div f_T` is a transposition; both transported rows come from the same pair of lemmas,
and `WeilPairingTelescopeTwo`'s `divisorProj_translateEndo_eq_neg` records that
`div (τ_T∗ f) = −div f`.  **That statement is false at `n = 3`** — the three points `O`, `(T)`,
`(−T)` are pairwise distinct and `τ_T` permutes them in a `3`-cycle, so no single translate is the
negative of `div f_T`.  Only the full three-fold product telescopes, which is why the third row
needs the genuinely affine action `mapProjPoint_translateAlgEquiv_pointClosedPoint_affine` and the
`3`-torsion relation `(−T) ⊕ (−T) = T` rather than `−T = T`.

Three factors are handled with two `divisorProj_mul` rewrites.  `divisorProj_prod` (`#643`) would
also serve, but a `Finset.range 3` formulation buys nothing here and costs the `mapDomain`
bookkeeping on a product with a distinguished `i = 0` term.

## A note on `[DecidableEq F]`

The telescoping carries `[DecidableEq F]` as an instance binder, exactly as its `n = 2` counterpart
does, so that it can be instantiated at a concrete base field — the non-vacuity section below needs
`instDecidableEqRat`, not a classical instance.  The `F(W)`-level torsion transport
`translatePoint_add_add_self` (`TranslationTorsionMap`) is stated under `open Classical in`
instead, so `translatePoint_neg_add_neg_of_three_torsion` replaces the ambient instance by the
classical one before invoking it; `DecidableEq` is a subsingleton, so this is `Subsingleton.elim`
and nothing more.  Doing it there, once, is what keeps the binder out of the two statements above
and off the non-vacuity certificate.

## Why it is projective

The affine `divisor W` does **not** transport under `translateEndo`: `τ_T` moves the point at
infinity into the affine chart.  That is the affine-chart caveat of `#409` and the reason `#658`
was done on `ProjPoint W`.  Everything below is `divisorProj`.

## What is *not* here

* Step A at `n = 3` — the general commutation `τ_P∗ ∘ [3]∗ = [3]∗ ∘ τ_T∗` for `[3]P = T`.  Only the
  degenerate `[3]T = O` case exists today (`TranslationTriplingComm`).
* The assembly, `e_3(T, T) = 1`, `#418`, `[3]∗`, `mulByThreeEndo`, `g_T` — none of them occurs in
  any statement below.
* `[IsAlgClosed F]`.  Deliberately absent: this half is true over any field, and the hypothesis
  belongs in the assembly, where it is used once to produce a point `P` with `[3]P = T` (by the
  merged `nsmul_three_surjective`, `Torsion/TriplingSurjective.lean`, `#690`).
* General `n`, the alternating property itself, antisymmetry.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(d), first product.
-/

open Polynomial IsDedekindDomain

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]
  [IsDedekindDomain W.CoordinateRing] {x₃ y₃ : F}

namespace CoordinateRing

/-! ### The group relation `(−T) ⊕ (−T) = T` over `F(W)` -/

omit [IsDedekindDomain W.CoordinateRing] in
/-- **`𝒯_{−T} + 𝒯_{−T} = 𝒯_T` for a `3`-torsion point.**  This is `3T = O` rearranged: from
`𝒯 + 𝒯 + 𝒯 = 0` one gets `𝒯 + 𝒯 = −𝒯`, hence `(−𝒯) + (−𝒯) = −(𝒯 + 𝒯) = 𝒯`.

It is the shape that `mapProjPoint_translateAlgEquiv_pointClosedPoint_affine` consumes, and it says
that translating the closed point of `T` by `−T` lands on the closed point of `−T`. -/
theorem translatePoint_neg_add_neg_of_three_torsion [inst : DecidableEq F] (h₃ : W.Equation x₃ y₃)
    (htors : torsionPoint h₃ + torsionPoint h₃ + torsionPoint h₃ = 0) :
    translatePoint ((W.equation_neg x₃ y₃).mpr h₃)
        + translatePoint ((W.equation_neg x₃ y₃).mpr h₃) = translatePoint h₃ := by
  -- `translatePoint_add_add_self` is stated under `open Classical in`, so its `htors` uses the
  -- classical decidability of equality on `F`; `DecidableEq` is a subsingleton, so the ambient
  -- instance can simply be replaced by that one.
  obtain rfl : inst = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  have hself : translatePoint h₃ + translatePoint h₃ = -translatePoint h₃ :=
    add_eq_zero_iff_eq_neg.mp (translatePoint_add_add_self h₃ htors)
  rw [translatePoint_neg h₃, ← neg_add, hself, neg_neg]

end CoordinateRing

/-! ### The two transported divisors -/

/-- **`div (τ_T∗ f) = n·O − n(−T)`** whenever `div f = n(T) − n·O`.

Translation by `T` sends the closed point of `T` to the point at infinity
(`mapProjPoint_translateAlgEquiv_pointClosedPoint`) and the point at infinity to the closed point
of `−T` (`mapProjPoint_translateAlgEquiv_none`), so the two coefficients move accordingly.  Stated
for an arbitrary `n : ℤ`; `n = 3` is the case the telescoping uses.

At `n = 2` this is `divisorProj_translateEndo_eq_neg`, because there `−T = T`. -/
theorem divisorProj_translateEndo_eq_none_sub_neg (h₃ : W.Equation x₃ y₃)
    {f : W.FunctionField} (hf : f ≠ 0) {n : ℤ}
    (hdiv : divisorProj W f
      = Finsupp.single (some (pointClosedPoint h₃)) n - Finsupp.single (none : ProjPoint W) n) :
    divisorProj W (translateEndo h₃ f)
      = Finsupp.single (none : ProjPoint W) n
        - Finsupp.single (some (pointClosedPoint ((W.equation_neg x₃ y₃).mpr h₃))) n := by
  rw [divisorProj_translateEndo h₃ hf, hdiv, Finsupp.mapDomain_sub, Finsupp.mapDomain_single,
    Finsupp.mapDomain_single, mapProjPoint_translateAlgEquiv_pointClosedPoint h₃,
    mapProjPoint_translateAlgEquiv_none h₃]

/-- **`div (τ_{−T}∗ f) = n(−T) − n(T)`** whenever `div f = n(T) − n·O` and `T` is `3`-torsion.

Translation by `−T` sends the point at infinity to the closed point of `T`
(`mapProjPoint_translateAlgEquiv_neg_none`, the double negation collapsing by `negY_negY`) and the
closed point of `T` to the closed point of `T ⊖ (−T) = 2T = −T`
(`mapProjPoint_translateAlgEquiv_pointClosedPoint_affine`).

This is the row that has no `n = 2` counterpart: it is where the `3`-torsion hypothesis is spent,
through `translatePoint_neg_add_neg_of_three_torsion`. -/
theorem divisorProj_translateEndo_neg_eq_neg_sub [DecidableEq F] (h₃ : W.Equation x₃ y₃)
    (htors : torsionPoint h₃ + torsionPoint h₃ + torsionPoint h₃ = 0)
    {f : W.FunctionField} (hf : f ≠ 0) {n : ℤ}
    (hdiv : divisorProj W f
      = Finsupp.single (some (pointClosedPoint h₃)) n - Finsupp.single (none : ProjPoint W) n) :
    divisorProj W (translateEndo ((W.equation_neg x₃ y₃).mpr h₃) f)
      = Finsupp.single (some (pointClosedPoint ((W.equation_neg x₃ y₃).mpr h₃))) n
        - Finsupp.single (some (pointClosedPoint h₃)) n := by
  rw [divisorProj_translateEndo _ hf, hdiv, Finsupp.mapDomain_sub, Finsupp.mapDomain_single,
    Finsupp.mapDomain_single, mapProjPoint_translateAlgEquiv_pointClosedPoint_affine h₃
      ((W.equation_neg x₃ y₃).mpr h₃) ((W.equation_neg x₃ y₃).mpr h₃)
      (translatePoint_neg_add_neg_of_three_torsion h₃ htors),
    mapProjPoint_translateAlgEquiv_neg_none h₃]

/-! ### The telescoping -/

/-- **The three-term telescoping.**  For a `3`-torsion point `T` there is a function `f_T` with
`div f_T = 3(T) − 3(O)` whose product with its translates by `T` and by `−T` is a nonzero constant.

This is the first of the two products of Silverman III.8.1(d), at `n = 3`.  It carries no
hypothesis beyond `T` being an affine `3`-torsion point: no `#418`, no algebraically closed base
field, no characteristic hypothesis. -/
theorem exists_mul_translateEndo_mul_translateEndo_eq_algebraMap [DecidableEq F]
    (h : W.Nonsingular x₃ y₃) (hP : Point.some x₃ y₃ h ∈ W.torsion 3) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (3 : ℤ)
        - Finsupp.single (none : ProjPoint W) (3 : ℤ) ∧
      ∃ c : F, c ≠ 0 ∧
        f * translateEndo h.left f
            * translateEndo ((W.equation_neg x₃ y₃).mpr h.left) f
          = algebraMap F W.FunctionField c := by
  have htors : torsionPoint h.left + torsionPoint h.left + torsionPoint h.left = 0 := by
    have h3 : (3 : ℕ) • (Point.some x₃ y₃ h : W.Point) = 0 := mem_torsion_iff.mp hP
    rwa [show (3 : ℕ) = 2 + 1 from rfl, add_smul, two_nsmul, one_nsmul] at h3
  obtain ⟨f, hf, hdiv⟩ := divisorProj_eq_single_sub_single_of_torsion h hP
  refine ⟨f, hf, hdiv, ?_⟩
  have hτ : translateEndo h.left f ≠ 0 :=
    fun hz => hf ((translateEndo h.left).injective (by rw [hz, map_zero]))
  have hτ' : translateEndo ((W.equation_neg x₃ y₃).mpr h.left) f ≠ 0 :=
    fun hz => hf ((translateEndo ((W.equation_neg x₃ y₃).mpr h.left)).injective
      (by rw [hz, map_zero]))
  refine (divisorProj_eq_zero_iff (mul_ne_zero (mul_ne_zero hf hτ) hτ')).mp ?_
  rw [divisorProj_mul (mul_ne_zero hf hτ) hτ', divisorProj_mul hf hτ,
    divisorProj_translateEndo_eq_none_sub_neg h.left hf hdiv,
    divisorProj_translateEndo_neg_eq_neg_sub h.left htors hf hdiv, hdiv]
  abel

/-! ### Non-vacuity

The telescoping is stated for an affine `3`-torsion point, and the whole file is conditional on
`[IsDedekindDomain W.CoordinateRing]`, so it is worth exhibiting a curve carrying such a point with
every instance discharged.  `WeilPairingTelescopeTwo`'s certificate `y² = x³ − x` will not serve:
it has no rational `3`-torsion.  The curve here is `y² + y = x³` over `ℚ`, of discriminant `−27`,
on which `(0, 0)` has order `3` — it is not fixed by negation (`negY 0 0 = −1`) and `Ψ₃` vanishes
at `0`, since `b₂ = b₄ = b₈ = 0`, so `Ψ₃ = 3X⁴ + 3b₆X` has no constant term. -/

section Nonvacuity

/-- The curve `y² + y = x³` over `ℚ`, of discriminant `-27`. -/
private def exampleCurveThree : Affine ℚ := ⟨0, 0, 1, 0, 0⟩

private instance : exampleCurveThree.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurveThree, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- `(0, 0)` is a nonsingular point of `y² + y = x³`. -/
private lemma exampleNonsingularThree : exampleCurveThree.Nonsingular 0 0 := by
  rw [nonsingular_iff]
  refine ⟨?_, Or.inr ?_⟩ <;> norm_num [exampleCurveThree, WeierstrassCurve.Affine.negY]

private lemma exampleTorsionThree :
    Point.some (0 : ℚ) 0 exampleNonsingularThree ∈ exampleCurveThree.torsion 3 := by
  rw [mem_torsion_three_some_iff (by norm_num [exampleCurveThree, WeierstrassCurve.Affine.negY])]
  norm_num [exampleCurveThree, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

example : ∃ f : exampleCurveThree.FunctionField, f ≠ 0 ∧
    divisorProj exampleCurveThree f
      = Finsupp.single (some (pointClosedPoint exampleNonsingularThree.left)) (3 : ℤ)
        - Finsupp.single (none : ProjPoint exampleCurveThree) (3 : ℤ) ∧
    ∃ c : ℚ, c ≠ 0 ∧
      f * translateEndo exampleNonsingularThree.left f
          * translateEndo ((exampleCurveThree.equation_neg 0 0).mpr
              exampleNonsingularThree.left) f
        = algebraMap ℚ exampleCurveThree.FunctionField c :=
  exists_mul_translateEndo_mul_translateEndo_eq_algebraMap exampleNonsingularThree
    exampleTorsionThree

end Nonvacuity

end WeierstrassCurve.Affine
