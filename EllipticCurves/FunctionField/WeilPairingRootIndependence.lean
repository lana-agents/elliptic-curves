/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.DivisorClassGroup
import EllipticCurves.FunctionField.TranslationComposition
import EllipticCurves.FunctionField.WeilPairingAlternatingThree

/-!
# The Weil-pairing element does not depend on which `n`-th root is chosen

The rung-5 root `g_S` is never constructed uniquely.  `exists_smul_pow_eq_of_nsmul_divisor`,
`exists_gS_two` and `exists_gS_three` (`NthRootOfPullback`) all produce it only up to a unit of
`F[W]`, because that is all the divisor determines (`exists_unit_of_divisor_eq`).  Consequently the
two merged alternating headlines

* `exists_weilPairingElt_self_eq_one_of_algClosed` (`WeilPairingAlternatingTwo`, `#688`),
* `exists_weilPairingElt_self_eq_one_of_algClosed_three` (`WeilPairingAlternatingThree`, `#719`),

quantify the root **existentially**: they say that *some* `n`-th root of `[n]∗ f_T` pairs trivially
with `T`.  That is weaker than "the Weil pairing is alternating", and it cannot be applied to a root
that arrives from elsewhere.

This file closes that gap.  It is fully ungated — no `hprin`, no rung 4, no Ward, no base change.

## The mechanism

`weilPairingElt h₂ g = τ_T∗ g / g`, so rescaling `g` by anything the translation fixes cancels:

```
weilPairingElt h₂ (a * g) = (τ_T∗ a · τ_T∗ g) / (a · g) = τ_T∗ g / g,       τ_T∗ a = a, a ≠ 0.
```

Both rescalings that can occur are of that kind, and both facts are already merged:

| what is fixed by `τ_T∗` | where |
| --- | --- |
| units of `F[W]` | `translateEndo_algebraMap_unit` (`WeilPairing`) |
| constants of `F` | `translateEndo_algebraMap_base` (`TranslationComposition`) |

Feeding that into the merged divisor-injectivity engine (`exists_unit_of_divisor_eq`, and its
`m`-fold form `exists_unit_of_nsmul_divisor_eq`) gives the statement the pairing needs: **two `n`-th
roots of the same function have the same Weil-pairing element.**

## Main results

* `weilPairingElt_mul_left_of_translateEndo_fixed` — the engine.  It needs no `g ≠ 0`: at `g = 0`
  both sides are `0 / 0 = 0`, and `mul_div_mul_left` is stated in that generality;
* `weilPairingElt_units_smul`, `weilPairingElt_algebraMap_mul` — the two instantiations;
* `divisor_units_smul` — rescaling by a unit does not move the divisor;
* `weilPairingElt_eq_of_divisor_eq`, `weilPairingElt_eq_of_nsmul_divisor_eq`;
* **`weilPairingElt_eq_of_smul_pow_eq`** — the payoff, in exactly the shape the rung-5 datum
  `u · g ^ n = [n]∗ f_S` comes in;
* **`exists_forall_weilPairingElt_self_eq_one_of_algClosed`** and
  **`exists_forall_weilPairingElt_self_eq_one_of_algClosed_three`** — the two headlines with the
  inner `∃ g` replaced by `∀ g`.

## What is deliberately still existential

The function `f = f_T` stays existential.  It too is pinned only up to a unit, but rescaling `f`
rescales `g` by an `n`-th root of a constant rather than by a constant, so quantifying over `f`
is a genuinely different statement that needs root extraction.  It is not attempted here.

## Not here

* Discharging `hprin` (`#418`), the descent of the `F̄`-statements to a general `F` (`#692`),
  antisymmetry, or anything at general `n`.
* The `μ_n` forms (`WeilPairingAlternatingMu`), which lift through
  `algebraMap_coe_rootsOfUnity_injective` and are a clean follow-on.

## Non-vacuity

Everything through `weilPairingElt_eq_of_smul_pow_eq` is ungated apart from the standing
`[IsDedekindDomain W.CoordinateRing]` of the divisor calculus (`#396`), and is instantiable
wherever that instance is.  The two headline corollaries inherit `hprin` from the theorems they
consume, so they admit no certificate on a concrete curve — for exactly the reason
`WeilPairingAlternatingTwo`'s own non-vacuity section gives, and no new one.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1.
-/

open Polynomial IsDedekindDomain

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic] {x₂ y₂ : F}

/-! ### Rescaling by something the translation fixes -/

/-- **The engine.**  If `a ≠ 0` is fixed by `τ_T∗ = translateEndo h₂`, then rescaling the rung-5
root by `a` leaves the Weil-pairing element unchanged:
`e_n(S, T)` computed from `a · g` equals `e_n(S, T)` computed from `g`.

No hypothesis on `g` is needed.  For `g = 0` both sides are `translateEndo h₂ 0 / 0 = 0`, and
`mul_div_mul_left` holds in that generality in a division ring. -/
theorem weilPairingElt_mul_left_of_translateEndo_fixed (h₂ : W.Equation x₂ y₂)
    {a : W.FunctionField} (ha : a ≠ 0) (hfix : translateEndo h₂ a = a) (g : W.FunctionField) :
    weilPairingElt h₂ (a * g) = weilPairingElt h₂ g := by
  rw [weilPairingElt, weilPairingElt, map_mul, hfix, mul_div_mul_left _ _ ha]

/-- **Rescaling by a unit of `F[W]` does not change the pairing element.**  The unit is a nonzero
constant, hence fixed by `translateEndo` (`translateEndo_algebraMap_unit`, the same fact that
discharges the `huf` input of `translateEndo_pow_eq_self_of`). -/
theorem weilPairingElt_units_smul (h₂ : W.Equation x₂ y₂) (u : W.CoordinateRingˣ)
    (g : W.FunctionField) :
    weilPairingElt h₂ ((u : W.CoordinateRing) • g) = weilPairingElt h₂ g := by
  rw [Algebra.smul_def]
  exact weilPairingElt_mul_left_of_translateEndo_fixed h₂
    (u.isUnit.map (algebraMap W.CoordinateRing W.FunctionField)).ne_zero
    (translateEndo_algebraMap_unit h₂ u) g

/-- **Rescaling by a nonzero constant of `F` does not change the pairing element.**  This is the
form the assemblies meet it in: `WeilPairingAlternatingTwo`/`Three` turn the unit `u` of `F[W]`
into a nonzero `c₀ : F` through `isUnit_iff_exists_eq_algebraMap` before doing any computation. -/
theorem weilPairingElt_algebraMap_mul (h₂ : W.Equation x₂ y₂) {c : F} (hc : c ≠ 0)
    (g : W.FunctionField) :
    weilPairingElt h₂ (algebraMap F W.FunctionField c * g) = weilPairingElt h₂ g :=
  weilPairingElt_mul_left_of_translateEndo_fixed h₂
    ((map_ne_zero_iff _ (algebraMap F W.FunctionField).injective).mpr hc)
    (translateEndo_algebraMap_base h₂ c) g

end CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]
  [IsDedekindDomain W.CoordinateRing] {x₂ y₂ : F}

open CoordinateRing

/-! ### From the divisor to the pairing element -/

omit [W.IsElliptic] in
/-- **Rescaling by a unit of `F[W]` does not move the divisor.**  A unit has no zeros and no poles
(`divisor_coe_units`), so the product rule leaves `divisor W g` alone.  As above, no hypothesis on
`g` is needed. -/
lemma divisor_units_smul (u : W.CoordinateRingˣ) (g : W.FunctionField) :
    divisor W ((u : W.CoordinateRing) • g) = divisor W g := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [smul_zero]
  · rw [Algebra.smul_def,
      divisor_mul (u.isUnit.map (algebraMap W.CoordinateRing W.FunctionField)).ne_zero hg,
      divisor_coe_units, zero_add]

/-- **The Weil-pairing element depends only on the divisor of the rung-5 root.**  Two nonzero
functions with the same divisor differ by a unit of `F[W]` (`exists_unit_of_divisor_eq`), and units
do not change the pairing element. -/
theorem weilPairingElt_eq_of_divisor_eq (h₂ : W.Equation x₂ y₂) {g₁ g₂ : W.FunctionField}
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (hdiv : divisor W g₁ = divisor W g₂) :
    weilPairingElt h₂ g₁ = weilPairingElt h₂ g₂ := by
  obtain ⟨u, hu⟩ := exists_unit_of_divisor_eq hg₁ hg₂ hdiv
  rw [← hu, weilPairingElt_units_smul]

/-- **It is enough that the `m`-fold divisors agree**, for `m ≠ 0`: the divisor group is
torsion-free, so `m • divisor W g₁ = m • divisor W g₂` already forces the divisors equal
(`exists_unit_of_nsmul_divisor_eq`). -/
theorem weilPairingElt_eq_of_nsmul_divisor_eq (h₂ : W.Equation x₂ y₂) {m : ℕ} (hm : m ≠ 0)
    {g₁ g₂ : W.FunctionField} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    (hdiv : m • divisor W g₁ = m • divisor W g₂) :
    weilPairingElt h₂ g₁ = weilPairingElt h₂ g₂ := by
  obtain ⟨u, hu⟩ := exists_unit_of_nsmul_divisor_eq hm hg₁ hg₂ hdiv
  rw [← hu, weilPairingElt_units_smul]

/-- **Two `n`-th roots of the same function give the same Weil-pairing element.**  This is the
statement in the shape the rung-5 datum comes in: `exists_smul_pow_eq_of_nsmul_divisor` and its
specialisations `exists_gS_two` / `exists_gS_three` deliver `u · g ^ m = [m]∗ f_S` with `u` a unit
of `F[W]`, and nothing pins `g` further.

Consequently `e_n(S, T)` is well defined by the rung-5 relation alone, which is what lets the
alternating headlines below quantify over *every* `n`-th root rather than a produced one. -/
theorem weilPairingElt_eq_of_smul_pow_eq (h₂ : W.Equation x₂ y₂) {m : ℕ} (hm : m ≠ 0)
    {g₁ g₂ h : W.FunctionField} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) {u₁ u₂ : W.CoordinateRingˣ}
    (hu₁ : (u₁ : W.CoordinateRing) • g₁ ^ m = h) (hu₂ : (u₂ : W.CoordinateRing) • g₂ ^ m = h) :
    weilPairingElt h₂ g₁ = weilPairingElt h₂ g₂ := by
  have e₁ : divisor W (g₁ ^ m) = divisor W h := by rw [← hu₁, divisor_units_smul]
  have e₂ : divisor W (g₂ ^ m) = divisor W h := by rw [← hu₂, divisor_units_smul]
  exact weilPairingElt_eq_of_nsmul_divisor_eq h₂ hm hg₁ hg₂
    (by rw [← divisor_pow, ← divisor_pow, e₁, e₂])

/-! ### The alternating headlines, for every `n`-th root

Both corollaries keep the hypotheses of the theorems they consume — `hprin` (`#418`) included and
unchanged — and only move the quantifier.  The alternating argument itself is not reproved. -/

open Classical in
/-- **`e_2(T, T) = 1` for every square root, over an algebraically closed field.**  The `∀ g` form
of `exists_weilPairingElt_self_eq_one_of_algClosed` (`#688`).

The `translateEndo h.left g = g` half is free: for a nonzero `g` it is *equivalent* to
`weilPairingElt h.left g = 1` by `weilPairingElt_eq_one_iff_translateEndo_fixed`, so only the
pairing value has to be transported, and `weilPairingElt_eq_of_smul_pow_eq` does that. -/
theorem exists_forall_weilPairingElt_self_eq_one_of_algClosed [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    (h : W.Nonsingular x₂ y₂) (htors : Point.some x₂ y₂ h ∈ W.torsion 2)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (2 : ℤ)
          - Finsupp.single (none : ProjPoint W) (2 : ℤ) ∧
        ∀ g : W.FunctionField, g ≠ 0 →
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) →
            translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 := by
  obtain ⟨f, hf, hdivproj, g₀, hg₀, ⟨u₀, hu₀⟩, -, hone⟩ :=
    exists_weilPairingElt_self_eq_one_of_algClosed h2 h htors hprin
  refine ⟨f, hf, hdivproj, fun g hg hgroot => ?_⟩
  obtain ⟨u, hu⟩ := hgroot
  have hval : weilPairingElt h.left g = 1 :=
    (weilPairingElt_eq_of_smul_pow_eq h.left two_ne_zero hg hg₀ hu hu₀).trans hone
  exact ⟨(weilPairingElt_eq_one_iff_translateEndo_fixed h.left hg).mp hval, hval⟩

open Classical in
/-- **`e_3(T, T) = 1` for every cube root, over an algebraically closed field.**  The `∀ g` form of
`exists_weilPairingElt_self_eq_one_of_algClosed_three` (`#719`), proved exactly as the `n = 2`
case. -/
theorem exists_forall_weilPairingElt_self_eq_one_of_algClosed_three [IsAlgClosed F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (h : W.Nonsingular x₂ y₂)
    (htors : Point.some x₂ y₂ h ∈ W.torsion 3)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (3 : ℤ)
          - Finsupp.single (none : ProjPoint W) (3 : ℤ) ∧
        ∀ g : W.FunctionField, g ≠ 0 →
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) →
            translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 := by
  obtain ⟨f, hf, hdivproj, g₀, hg₀, ⟨u₀, hu₀⟩, -, hone⟩ :=
    exists_weilPairingElt_self_eq_one_of_algClosed_three h2 h3 h htors hprin
  refine ⟨f, hf, hdivproj, fun g hg hgroot => ?_⟩
  obtain ⟨u, hu⟩ := hgroot
  have hval : weilPairingElt h.left g = 1 :=
    (weilPairingElt_eq_of_smul_pow_eq h.left three_ne_zero hg hg₀ hu hu₀).trans hone
  exact ⟨(weilPairingElt_eq_one_iff_translateEndo_fixed h.left hg).mp hval, hval⟩

/-! ### Non-vacuity

The `CoordinateRing`-namespace results above carry no hypothesis beyond `[W.IsElliptic]` and a
`W.Equation` for the translation point, so they *can* be instantiated on a concrete curve, and are
below.  `y² = x³ − x` over `AlgebraicClosure ℚ` with `T = (0, 0)` is the same certificate curve
`WeilPairingAlternatingTwo` uses.

The divisor-level results additionally need `[IsDedekindDomain W.CoordinateRing]` (`#396`) and the
two headline corollaries need `hprin` (`#418`); neither is available on any concrete curve in this
tree, which is why the sibling gated files carry no certificate either. -/

section Nonvacuity

/-- An algebraically closed field of characteristic zero. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

/-- The curve `y² = x³ − x` over `AlgebraicClosure ℚ`, of discriminant `64`. -/
private noncomputable def exampleCurve : Affine exampleField := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- `T = (0, 0)` lies on `y² = x³ − x`. -/
private lemma exampleEquation : exampleCurve.Equation 0 0 := by
  rw [equation_iff]
  norm_num [exampleCurve]

/-- Rescaling by a nonzero constant really does leave the pairing element alone, on a curve that
exists. -/
example (c : exampleField) (hc : c ≠ 0) (g : exampleCurve.FunctionField) :
    weilPairingElt exampleEquation (algebraMap exampleField exampleCurve.FunctionField c * g)
      = weilPairingElt exampleEquation g :=
  weilPairingElt_algebraMap_mul exampleEquation hc g

/-- The same for a unit of the coordinate ring. -/
example (u : exampleCurve.CoordinateRingˣ) (g : exampleCurve.FunctionField) :
    weilPairingElt exampleEquation ((u : exampleCurve.CoordinateRing) • g)
      = weilPairingElt exampleEquation g :=
  weilPairingElt_units_smul exampleEquation u g

end Nonvacuity

end WeierstrassCurve.Affine
