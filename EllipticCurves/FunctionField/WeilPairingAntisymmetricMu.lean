/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairingAntisymmetric
import EllipticCurves.FunctionField.WeilPairingBilinearMu
import EllipticCurves.Torsion.ThreeTorsion

/-!
# Divisor-slot bilinearity and antisymmetry at the `μ_n(F)` group level (rung 6)

Let `W` be an elliptic curve over a field `F`.  The four named structural properties of the
divisor-theoretic Weil-pairing element (`WeilPairing.lean`, `#419`)

```
e_n(S, T) := weilPairingElt h_T g_S = τ_T∗(g_S) / g_S,   τ_T∗ = translateEndo h_T,
```

are all merged, but as equations *in the function field* `F(W)`.  The honest value group of the
Weil pairing is `μ_n(F) = rootsOfUnity n F ≤ Fˣ` (Silverman *AEC* III.8), and two of the four have
already been lifted to it:

* translation-slot bilinearity — `weilPairingElt_translatePoint_add_of_baseField` (`#451`) lifts
  to `weilPairingMu_translatePoint_add_of_baseField` (`WeilPairingBilinearMu`, `#459`);
* the alternating reduction — `weilPairingElt_eq_one_iff_translateEndo_fixed` (`#465`) lifts to
  `weilPairingMu_eq_one_iff_translateEndo_fixed` (`WeilPairingAlternatingMu`);
* divisor-slot multiplicativity and bilinearity — `weilPairingElt_mul` /
  `weilPairingElt_divisorSlot_add` (`#723`): **this file**;
* antisymmetry — `weilPairingElt_mul_swap_eq_one` / `weilPairingElt_eq_inv` (`#723`): **this
  file**.

This file supplies the remaining two rows: multiplicativity and bilinearity in the **divisor** slot,
and **antisymmetry** `e_n(T, S) = e_n(S, T)⁻¹`, as genuine equations in the group
`rootsOfUnity n F`.  At that level the inverse in the antisymmetry headline is the *group* inverse,
not the field division `x⁻¹` of `F(W)`.

## The route

`weilPairingMu` lands in the subgroup `rootsOfUnity n F ≤ Fˣ`, so any equation between two of its
values is proved by applying the injective composite

```lean
algebraMap_coe_rootsOfUnity_injective :
    Function.Injective (fun ζ : rootsOfUnity n F => algebraMap F W.FunctionField ((ζ : Fˣ) : F))
```

(`WeilPairingBilinearMu.lean`, `#459`), pushing `Subgroup.coe_mul` / `Units.val_mul` / `map_mul`
(resp. their inverse forms) through, rewriting each `weilPairingMu` back into its `weilPairingElt`
by the defining property `algebraMap_coe_weilPairingMu` (`#457`), and closing with the merged
`F(W)`-level theorem.  No file below reproves anything; every proof is that one descent.

Note that `weilPairingMu h₂ hpow` depends on the *proof* `hpow` only up to proof irrelevance, so a
`hpow` datum may freely be replaced by any propositionally equal one.

## Main results

* `weilPairingMu_eq_one_iff` — `weilPairingMu h₂ hpow = 1 ↔ weilPairingElt h₂ g = 1`.  **No
  `g ≠ 0` hypothesis**, unlike `weilPairingMu_eq_one_iff_translateEndo_fixed`, which has to compare
  `τ g` with `g`.  This is the workhorse: it turns every `F(W)`-level "contributes `1`" fact into a
  `μ_n(F)` one, and it is what converts between the two equivalent phrasings of the alternating
  inputs to antisymmetry;
* `weilPairingMu_mul`, `weilPairingMu_inv` — multiplicativity of the divisor slot in the group;
* `weilPairingMu_algebraMap`, `weilPairingMu_mulByTwoEndo_of_baseField`,
  `weilPairingMu_mulByThreeEndo_of_baseField` — the correction factors contribute the group
  identity;
* **`weilPairingMu_divisorSlot_add`** — divisor-slot bilinearity in `μ_n(F)`, with the concrete
  `_const` / `_two` / `_three` corollaries;
* **`weilPairingMu_mul_swap_eq_one`** and **`weilPairingMu_eq_inv`** — antisymmetry in `μ_n(F)`, in
  product and inverse form.

## Scope

`[Field F] {W : Affine F} [W.IsElliptic]` throughout, together with the `[NeZero n]` that
`weilPairingMu` itself carries.  **No `[IsDedekindDomain W.CoordinateRing]`, no `[IsAlgClosed F]`,
no `#418`, no rung 4, no Ward.**  Every carried input of `#723` — the product relation
`hprod : g_R = g_S · g_T · w` and the alternating values — is passed through as a hypothesis in
exactly the form `#723` states it.  ⚠️ `hprod` is **not** rung-4 gated, as this bullet used to
say; it is produced from rung-5 data in
`EllipticCurves.FunctionField.WeilPairingProductRelation` (`#845`).  The gate does not move and
no new
gate is added.

⚠️ As in `#723`, **the alternating property is an input at three points, `S`, `T` and `R = S ⊕ T`,
not two.**  `e_n(g_R, T_R) = 1` is a hypothesis of `weilPairingMu_mul_swap_eq_one`; antisymmetry
consumes the alternating property and never proves it.  Only one of the three instances needs the
divisor-slot step, which is why `e_n(w, S)` and `e_n(w, T)` never appear.  Over an algebraically
closed field all three come from a single merged theorem applied at three different points, so this
is not three separate gates.

The alternating inputs are stated at the `F(W)` level (`weilPairingElt … = 1`) rather than as
`weilPairingMu … = 1`, because that form needs no extra `hpow` datum per point; the two are
interchangeable in one rewrite through `weilPairingMu_eq_one_iff`.

Out of scope: producing `hprod` or any alternating input; bundling `e_n` as a `MonoidHom` into
`μ_n(F)` in either slot (that needs a `hpow` datum uniform in the slot variable, a different
statement); Galois-equivariance (`#456`); the descent to a general `F` (`#692`); non-degeneracy,
which is **not** Ward-gated — `WeilPairing`'s scope section is the canonical account of what it
consumes (`#769`).

## Non-vacuity

Everything up to and including the two pullback lemmas is unconditional or carries only merged
hypotheses, and every one of them is instantiated below.  The `[2]∗` instances use `y² = x³ − x`
over `AlgebraicClosure ℚ` with `T = (0, 0)` — the certificate curve `WeilPairingAlternatingTwo` and
`WeilPairingRootIndependence` use, on which `T` is `2`-torsion.  The `[3]∗` instance cannot live
there, since that `T` has order `2` and `weilPairingMu_mulByThreeEndo_of_baseField`'s `htors` would
be *false*; it uses instead `y² + y = x³` with `T = (0, 0)`, of order `3`, which is
`WeilPairingAlternatingThree`'s certificate curve.  Four of the instances are closed outright, with
no hypothesis left over: `weilPairingMu` evaluated at the constant functions `1` and
`algebraMap c`, at `[2]∗1` and at `[3]∗1` is the identity of the group, not merely an element whose
square (resp. cube) is `1`.  The multiplicativity and inverse instances keep only the `hpow` data
that `weilPairingMu` needs in order to be formed at all.

`weilPairingMu_divisorSlot_add` and the antisymmetry headlines inherit `hprod` and the alternating
values, and so are not instantiated **here**, for exactly the reason
`WeilPairingAntisymmetric.lean`'s own non-vacuity section gives.  ⚠️ That is a fact about these two
files and not an obstruction: `hprod` follows from rung-5 data
(`WeilPairingProductRelation.exists_prod_eq_of_pullback`, `#845`) and the alternating inputs are
unconditional over `F̄` at both `n`, so the `F(W)`-level headlines *are* instantiated there, and
the two `μ_n` antisymmetry headlines are instantiated against them in
`EllipticCurves.FunctionField.WeilPairingProductRelationMu` (`#855`), downstream of this file.
The `_const` / `_two` / `_three` corollaries do exhibit correction factors `w`
for which the hypothesis `e_n(w, T) = 1` is *proved* rather than assumed, so
`weilPairingMu_divisorSlot_add` has content beyond `w = 1`.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(a) (bilinearity) and
  III.8.1(d) (alternating, hence antisymmetric); III.8 for the value group `μ_n`.
-/

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-! ### Manufacturing the root-of-unity data

`weilPairingMu` consumes a proof of `e_n(g, T) ^ n = 1`.  The two lemmas here produce that datum
for a product and for an inverse out of the data for the factors, so that a caller is never forced
to *assume* what multiplicativity already gives. -/

/-- **`e_n(g, T) = 1` for the constant function `1`.**  `τ_T∗` is a ring homomorphism, so
`e_n(1, T) = 1 / 1 = 1`.  Recorded here because it is the unit of the divisor-slot multiplicativity
`weilPairingElt_mul`, and because it supplies a `hpow` datum with no hypotheses at all. -/
@[simp]
theorem weilPairingElt_one {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) :
    weilPairingElt h₂ (1 : W.FunctionField) = 1 := by
  simp only [weilPairingElt, map_one, div_one]

/-- The root-of-unity datum for a product, from the data for the two factors.  Immediate from
`weilPairingElt_mul` and `mul_pow`; no nonvanishing hypothesis. -/
theorem weilPairingElt_mul_pow_eq_one {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    {g₁ g₂ : W.FunctionField} {n : ℕ} (hpow₁ : weilPairingElt h₂ g₁ ^ n = 1)
    (hpow₂ : weilPairingElt h₂ g₂ ^ n = 1) :
    weilPairingElt h₂ (g₁ * g₂) ^ n = 1 := by
  rw [weilPairingElt_mul, mul_pow, hpow₁, hpow₂, one_mul]

/-- The root-of-unity datum for an inverse, from the datum for the element.  Immediate from
`weilPairingElt_inv` and `inv_pow`. -/
theorem weilPairingElt_inv_pow_eq_one {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    {g : W.FunctionField} {n : ℕ} (hpow : weilPairingElt h₂ g ^ n = 1) :
    weilPairingElt h₂ g⁻¹ ^ n = 1 := by
  rw [weilPairingElt_inv, inv_pow, hpow, inv_one]

/-! ### The workhorse: being the group identity is being `1` in `F(W)` -/

/-- **`weilPairingMu` is the group identity of `μ_n(F)` exactly when the pairing element is `1` in
`F(W)`.**

```
weilPairingMu h₂ hpow = 1 ↔ weilPairingElt h₂ g = 1.
```

Unlike `weilPairingMu_eq_one_iff_translateEndo_fixed` (`WeilPairingAlternatingMu.lean`) this needs
**no `g ≠ 0` hypothesis**: the comparison is between `weilPairingElt` and `1`, and never between
`τ_T∗ g` and `g`, so the degenerate case `g = 0` — where `e_n(0, T) = 0 / 0 = 0 ≠ 1` — is decided
correctly on both sides rather than excluded.

Both directions are the injective composite `ζ ↦ algebraMap F F(W) ((ζ : Fˣ) : F)`
(`algebraMap_coe_rootsOfUnity_injective`, `#459`) together with the defining property
`algebraMap_coe_weilPairingMu` (`#457`) and `algebraMap F F(W) 1 = 1`. -/
theorem weilPairingMu_eq_one_iff {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {g : W.FunctionField}
    {n : ℕ} [NeZero n] (hpow : weilPairingElt h₂ g ^ n = 1) :
    weilPairingMu h₂ hpow = 1 ↔ weilPairingElt h₂ g = 1 := by
  constructor
  · intro h
    have := congrArg
      (fun ζ : rootsOfUnity n F => algebraMap F W.FunctionField ((ζ : Fˣ) : F)) h
    simpa only [algebraMap_coe_weilPairingMu, OneMemClass.coe_one, Units.val_one, map_one]
      using this
  · intro h
    refine algebraMap_coe_rootsOfUnity_injective (W := W) ?_
    simp only [algebraMap_coe_weilPairingMu, OneMemClass.coe_one, Units.val_one, map_one]
    exact h

/-! ### Multiplicativity in the divisor slot, in the group -/

/-- **The divisor slot of `weilPairingMu` is multiplicative, in the group `μ_n(F)`.**

```
weilPairingMu(g₁ · g₂, T) = weilPairingMu(g₁, T) · weilPairingMu(g₂, T).
```

The group-level form of `weilPairingElt_mul` (`#723`), which is itself hypothesis-free — not even
`g₁, g₂ ≠ 0` — so this is too, beyond the three `hpow` data that `weilPairingMu` needs in order to
exist.  `weilPairingElt_mul_pow_eq_one` manufactures the third from the first two. -/
theorem weilPairingMu_mul {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {g₁ g₂ : W.FunctionField} {n : ℕ}
    [NeZero n] (hpow₁ : weilPairingElt h₂ g₁ ^ n = 1) (hpow₂ : weilPairingElt h₂ g₂ ^ n = 1)
    (hpow : weilPairingElt h₂ (g₁ * g₂) ^ n = 1) :
    weilPairingMu h₂ hpow = weilPairingMu h₂ hpow₁ * weilPairingMu h₂ hpow₂ := by
  refine algebraMap_coe_rootsOfUnity_injective (W := W) ?_
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul, algebraMap_coe_weilPairingMu]
  exact weilPairingElt_mul h₂ g₁ g₂

/-- **The divisor slot of `weilPairingMu` takes inverses to group inverses.**

```
weilPairingMu(g⁻¹, T) = (weilPairingMu(g, T))⁻¹.
```

The group-level form of `weilPairingElt_inv` (`#723`).  On the right the inverse is taken in
`μ_n(F)`; the descent turns it into the field inverse of `F(W)`. -/
theorem weilPairingMu_inv {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {g : W.FunctionField} {n : ℕ}
    [NeZero n] (hpow : weilPairingElt h₂ g ^ n = 1)
    (hpowInv : weilPairingElt h₂ g⁻¹ ^ n = 1) :
    weilPairingMu h₂ hpowInv = (weilPairingMu h₂ hpow)⁻¹ := by
  refine algebraMap_coe_rootsOfUnity_injective (W := W) ?_
  simp only [Subgroup.coe_inv, Units.val_inv_eq_inv_val, map_inv₀, algebraMap_coe_weilPairingMu]
  exact weilPairingElt_inv h₂ g

/-! ### The correction factors contribute the group identity -/

/-- **A nonzero constant contributes the identity of `μ_n(F)`.**  `weilPairingElt_algebraMap`
(`#723`) through `weilPairingMu_eq_one_iff`. -/
theorem weilPairingMu_algebraMap {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {c : F} (hc : c ≠ 0) {n : ℕ}
    [NeZero n] (hpow : weilPairingElt h₂ (algebraMap F W.FunctionField c) ^ n = 1) :
    weilPairingMu h₂ hpow = 1 :=
  (weilPairingMu_eq_one_iff h₂ hpow).mpr (weilPairingElt_algebraMap h₂ hc)

variable {xT yT : F}

open Classical in
/-- **A `[2]∗`-pullback contributes the identity of `μ_n(F)`, for a `2`-torsion translation
point.**  `weilPairingElt_mulByTwoEndo_of_baseField` (`#723`, off the merged `hcomm` discharge
`translateEndo_mulByTwoEndo_apply`, `#164`) through `weilPairingMu_eq_one_iff`. -/
theorem weilPairingMu_mulByTwoEndo_of_baseField (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0)
    (htors : torsionPoint hT + torsionPoint hT = 0) {f : W.FunctionField} (hf : f ≠ 0) {n : ℕ}
    [NeZero n] (hpow : weilPairingElt hT (mulByTwoEndo h2 f) ^ n = 1) :
    weilPairingMu hT hpow = 1 :=
  (weilPairingMu_eq_one_iff hT hpow).mpr
    (weilPairingElt_mulByTwoEndo_of_baseField hT h2 htors hf)

open Classical in
/-- **A `[3]∗`-pullback contributes the identity of `μ_n(F)`, for a `3`-torsion translation
point.**  The `mulByThreeEndo` mirror of `weilPairingMu_mulByTwoEndo_of_baseField`. -/
theorem weilPairingMu_mulByThreeEndo_of_baseField (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0)
    (htors : torsionPoint hT + torsionPoint hT + torsionPoint hT = 0) {f : W.FunctionField}
    (hf : f ≠ 0) {n : ℕ} [NeZero n]
    (hpow : weilPairingElt hT (mulByThreeEndo h2 h3 f) ^ n = 1) :
    weilPairingMu hT hpow = 1 :=
  (weilPairingMu_eq_one_iff hT hpow).mpr
    (weilPairingElt_mulByThreeEndo_of_baseField hT h2 h3 htors hf)

/-! ### Bilinearity in the divisor slot, in the group -/

/-- **Bilinearity of `weilPairingMu` in the divisor slot.**  Given the product relation

```
hprod : g_R = g_S · g_T · w        (for  S ⊕ T = R)
```

and that the correction factor is invisible to the pairing (`hw : e_n(w, T) = 1`),

```
weilPairingMu(g_R, T) = weilPairingMu(g_S, T) · weilPairingMu(g_T, T)   in μ_n(F).
```

The group-level form of `weilPairingElt_divisorSlot_add` (`#723`).  `hprod` is the single gated
input and is **not** produced here (⚠️ rung 5 only — it is produced in
`EllipticCurves.FunctionField.WeilPairingProductRelation`, `#845`); `hw` is discharged outright
in the
corollaries below. -/
theorem weilPairingMu_divisorSlot_add {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    {gS gT gR w : W.FunctionField} (hprod : gR = gS * gT * w)
    (hw : weilPairingElt h₂ w = 1) {n : ℕ} [NeZero n]
    (hpowS : weilPairingElt h₂ gS ^ n = 1) (hpowT : weilPairingElt h₂ gT ^ n = 1)
    (hpowR : weilPairingElt h₂ gR ^ n = 1) :
    weilPairingMu h₂ hpowR = weilPairingMu h₂ hpowS * weilPairingMu h₂ hpowT := by
  refine algebraMap_coe_rootsOfUnity_injective (W := W) ?_
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul, algebraMap_coe_weilPairingMu]
  exact weilPairingElt_divisorSlot_add h₂ hprod hw

/-- **Divisor-slot bilinearity in `μ_n(F)` when the correction factor is a nonzero constant.**  The
cheapest instance of `weilPairingMu_divisorSlot_add` with `hw` proved rather than assumed: it is
`weilPairingElt_algebraMap`, and no torsion hypothesis on the translation point is needed. -/
theorem weilPairingMu_divisorSlot_add_const {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    {gS gT gR : W.FunctionField} {c : F} (hc : c ≠ 0)
    (hprod : gR = gS * gT * algebraMap F W.FunctionField c) {n : ℕ} [NeZero n]
    (hpowS : weilPairingElt h₂ gS ^ n = 1) (hpowT : weilPairingElt h₂ gT ^ n = 1)
    (hpowR : weilPairingElt h₂ gR ^ n = 1) :
    weilPairingMu h₂ hpowR = weilPairingMu h₂ hpowS * weilPairingMu h₂ hpowT :=
  weilPairingMu_divisorSlot_add h₂ hprod (weilPairingElt_algebraMap h₂ hc) hpowS hpowT hpowR

open Classical in
/-- **Divisor-slot bilinearity in `μ_n(F)` at `n = 2`, with the classical correction factor.**
Here `w = c · [2]∗f` is the shape Silverman's `g_{S ⊕ T} = c · g_S · g_T · (h ∘ [2])` produces, and
`hw` is discharged by `weilPairingElt_algebraMap` together with
`weilPairingElt_mulByTwoEndo_of_baseField`. -/
theorem weilPairingMu_divisorSlot_add_two (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0)
    (htors : torsionPoint hT + torsionPoint hT = 0)
    {gS gT gR f : W.FunctionField} {c : F} (hc : c ≠ 0) (hf : f ≠ 0)
    (hprod : gR = gS * gT * (algebraMap F W.FunctionField c * mulByTwoEndo h2 f)) {n : ℕ}
    [NeZero n] (hpowS : weilPairingElt hT gS ^ n = 1) (hpowT : weilPairingElt hT gT ^ n = 1)
    (hpowR : weilPairingElt hT gR ^ n = 1) :
    weilPairingMu hT hpowR = weilPairingMu hT hpowS * weilPairingMu hT hpowT :=
  weilPairingMu_divisorSlot_add hT hprod
    (by
      rw [weilPairingElt_mul, weilPairingElt_algebraMap hT hc,
        weilPairingElt_mulByTwoEndo_of_baseField hT h2 htors hf, mul_one])
    hpowS hpowT hpowR

open Classical in
/-- **Divisor-slot bilinearity in `μ_n(F)` at `n = 3`, with the classical correction factor.**  The
`mulByThreeEndo` mirror of `weilPairingMu_divisorSlot_add_two`. -/
theorem weilPairingMu_divisorSlot_add_three (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (htors : torsionPoint hT + torsionPoint hT + torsionPoint hT = 0)
    {gS gT gR f : W.FunctionField} {c : F} (hc : c ≠ 0) (hf : f ≠ 0)
    (hprod : gR = gS * gT * (algebraMap F W.FunctionField c * mulByThreeEndo h2 h3 f)) {n : ℕ}
    [NeZero n] (hpowS : weilPairingElt hT gS ^ n = 1) (hpowT : weilPairingElt hT gT ^ n = 1)
    (hpowR : weilPairingElt hT gR ^ n = 1) :
    weilPairingMu hT hpowR = weilPairingMu hT hpowS * weilPairingMu hT hpowT :=
  weilPairingMu_divisorSlot_add hT hprod
    (by
      rw [weilPairingElt_mul, weilPairingElt_algebraMap hT hc,
        weilPairingElt_mulByThreeEndo_of_baseField hT h2 h3 htors hf, mul_one])
    hpowS hpowT hpowR

/-! ### Antisymmetry in `μ_n(F)` -/

open Classical in
/-- **Antisymmetry of the Weil pairing in `μ_n(F)`, in product form.**

```
weilPairingMu(S, T) · weilPairingMu(T, S) = 1   in rootsOfUnity n F.
```

The group-level form of `weilPairingElt_mul_swap_eq_one` (`#723`), whose hypotheses are carried
through unchanged:

* `hadd` — the base-field group relation `S ⊕ T = R`;
* `hprod`/`hwR` — the divisor-slot datum **at `R` only**; `e_n(w, S)` and `e_n(w, T)` never appear;
* `hpowTS` — the root-of-unity datum for `e_n(g_S, T)`, which the merged translation-slot
  bilinearity consumes.  `hpowST` is needed only to form the left-hand `weilPairingMu`;
* `haltS`, `haltT`, `haltR` — the **alternating property at `S`, at `T` and at `R`**, all three
  hypotheses.  Antisymmetry consumes the alternating property; it does not prove it anywhere.  They
  are stated at the `F(W)` level, which needs no further `hpow` datum; `weilPairingMu_eq_one_iff`
  converts each to `weilPairingMu … = 1` in one rewrite. -/
theorem weilPairingMu_mul_swap_eq_one {xS yS xR yR : F}
    (hS : W.Equation xS yS) (hT : W.Equation xT yT) (hR : W.Equation xR yR)
    (hadd : torsionPoint hS + torsionPoint hT = torsionPoint hR)
    {gS gT gR w : W.FunctionField} (hgS : gS ≠ 0) (hgT : gT ≠ 0)
    (hprod : gR = gS * gT * w) (hwR : weilPairingElt hR w = 1) {n : ℕ} [NeZero n]
    (hpowTS : weilPairingElt hT gS ^ n = 1) (hpowST : weilPairingElt hS gT ^ n = 1)
    (haltS : weilPairingElt hS gS = 1) (haltT : weilPairingElt hT gT = 1)
    (haltR : weilPairingElt hR gR = 1) :
    weilPairingMu hS hpowST * weilPairingMu hT hpowTS = 1 := by
  refine algebraMap_coe_rootsOfUnity_injective (W := W) ?_
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul, algebraMap_coe_weilPairingMu,
    OneMemClass.coe_one, Units.val_one, map_one]
  exact weilPairingElt_mul_swap_eq_one hS hT hR hadd hgS hgT hprod hwR (NeZero.ne n) hpowTS
    haltS haltT haltR

open Classical in
/-- **Antisymmetry in `μ_n(F)`, in the quotable inverse form** `e_n(T, S) = (e_n(S, T))⁻¹`.

```
weilPairingMu(S, T) = (weilPairingMu(T, S))⁻¹   in rootsOfUnity n F.
```

Immediate from `weilPairingMu_mul_swap_eq_one` by `eq_inv_of_mul_eq_one_left` **in the group**
`rootsOfUnity n F` — this is the group inverse, not a transport of the field division of `F(W)`,
which is what makes the `μ_n` form the one worth quoting. -/
theorem weilPairingMu_eq_inv {xS yS xR yR : F}
    (hS : W.Equation xS yS) (hT : W.Equation xT yT) (hR : W.Equation xR yR)
    (hadd : torsionPoint hS + torsionPoint hT = torsionPoint hR)
    {gS gT gR w : W.FunctionField} (hgS : gS ≠ 0) (hgT : gT ≠ 0)
    (hprod : gR = gS * gT * w) (hwR : weilPairingElt hR w = 1) {n : ℕ} [NeZero n]
    (hpowTS : weilPairingElt hT gS ^ n = 1) (hpowST : weilPairingElt hS gT ^ n = 1)
    (haltS : weilPairingElt hS gS = 1) (haltT : weilPairingElt hT gT = 1)
    (haltR : weilPairingElt hR gR = 1) :
    weilPairingMu hS hpowST = (weilPairingMu hT hpowTS)⁻¹ :=
  eq_inv_of_mul_eq_one_left
    (weilPairingMu_mul_swap_eq_one hS hT hR hadd hgS hgT hprod hwR hpowTS hpowST
      haltS haltT haltR)

/-! ### Non-vacuity

The results above that carry no hypothesis beyond `[W.IsElliptic]`, a `W.Equation` for the
translation point and the `hpow` data can be instantiated on a concrete curve, and all of them are
below.  Two curves are needed, because the pullback lemmas constrain the *order* of `T`:

* `y² = x³ − x` over `AlgebraicClosure ℚ` with `T = (0, 0)` — the certificate curve
  `WeilPairingAlternatingTwo` and `WeilPairingRootIndependence` use.  Here `T` is `2`-torsion
  (`negY 0 0 = 0`, so `T = −T`), which is what `weilPairingMu_mulByTwoEndo_of_baseField` wants;
* `y² + y = x³` over the same field, again with `T = (0, 0)` — `WeilPairingAlternatingThree`'s
  certificate curve.  Here `negY 0 0 = −1 ≠ 0` and `Ψ₃` vanishes at `0`, so `T` has order exactly
  `3` and `weilPairingMu_mulByThreeEndo_of_baseField` applies.

The second curve is not decoration: on the first one that lemma's `htors` is **false**, since a
point of order `2` is not of order `3`.  A `[3]∗` certificate on `y² = x³ − x` would be a fiction,
so the honest move is a second curve rather than a silent omission.

`weilPairingMu_divisorSlot_add` and the two antisymmetry headlines additionally need the product
relation `hprod` and the alternating values.  ⚠️ Both are now available over `F̄` at `n = 2` and
`n = 3` — `hprod` from rung-5 data (`WeilPairingProductRelation`, `#845`), the alternating values
from `#801`/`#829` — and that file carries concrete certificates for the `F(W)`-level headlines on
named torsion points.  The two `μ_n` **antisymmetry** headlines are instantiated against them in
`EllipticCurves.FunctionField.WeilPairingProductRelationMu` (`#855`), which imports this file:
`exists_weilPairingMu_mul_swap_eq_one_{two,three}` and `exists_weilPairingMu_eq_inv_{two,three}`
carry no hypothesis beyond `[IsAlgClosed F]` and the setting, and are certified on the same two
curves used there.

⚠️ `weilPairingMu_divisorSlot_add` is **not** instantiated by that file, and the reason is the
shape of the existential rather than a missing input: it needs the third root `g_R` and the
correction factor `w` as data, and `#845`'s headlines quantify both away inside their own proofs
and expose only `g_S` and `g_T`.  `exists_prod_eq_of_pullback` does produce them, so what is
wanted is a headline with a wider envelope, not new mathematics; that is a separate statement and
is not attempted in `#855`. -/

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

/-- The root-of-unity datum at the constant function `1`, on a curve that exists. -/
private lemma examplePowOne :
    weilPairingElt exampleEquation (1 : exampleCurve.FunctionField) ^ 2 = 1 := by
  rw [weilPairingElt_one, one_pow]

/-- On a curve that exists, the `μ_2`-packaged pairing value at the constant function `1` really is
the identity of the group `μ_2(F̄)` — not merely an element whose square is `1`. -/
example : weilPairingMu exampleEquation examplePowOne = 1 :=
  (weilPairingMu_eq_one_iff exampleEquation examplePowOne).mpr
    (weilPairingElt_one exampleEquation)

/-- The root-of-unity datum at a nonzero constant of the base field. -/
private lemma examplePowConst {c : exampleField} (hc : c ≠ 0) :
    weilPairingElt exampleEquation
      (algebraMap exampleField exampleCurve.FunctionField c) ^ 2 = 1 := by
  rw [weilPairingElt_algebraMap exampleEquation hc, one_pow]

/-- The same for a nonzero constant of the base field, through `weilPairingMu_algebraMap`, and
again with no hypothesis beyond `c ≠ 0`. -/
example {c : exampleField} (hc : c ≠ 0) :
    weilPairingMu exampleEquation (examplePowConst hc) = 1 :=
  weilPairingMu_algebraMap exampleEquation hc _

/-- Multiplicativity of the divisor slot, in the group, on a curve that exists. -/
example {g₁ g₂ : exampleCurve.FunctionField}
    (hpow₁ : weilPairingElt exampleEquation g₁ ^ 2 = 1)
    (hpow₂ : weilPairingElt exampleEquation g₂ ^ 2 = 1) :
    weilPairingMu exampleEquation (weilPairingElt_mul_pow_eq_one exampleEquation hpow₁ hpow₂)
      = weilPairingMu exampleEquation hpow₁ * weilPairingMu exampleEquation hpow₂ :=
  weilPairingMu_mul exampleEquation hpow₁ hpow₂ _

/-- Group inverses, on a curve that exists. -/
example {g : exampleCurve.FunctionField} (hpow : weilPairingElt exampleEquation g ^ 2 = 1) :
    weilPairingMu exampleEquation (weilPairingElt_inv_pow_eq_one exampleEquation hpow)
      = (weilPairingMu exampleEquation hpow)⁻¹ :=
  weilPairingMu_inv exampleEquation hpow _

/-! #### The `[2]∗` pullback: `T = (0, 0)` on `y² = x³ − x` is `2`-torsion -/

private lemma exampleTwoNeZero : (2 : exampleField) ≠ 0 := by norm_num

open Classical in
/-- `T = (0, 0)` is `2`-torsion on `y² = x³ − x`: the curve has `a₁ = a₃ = 0`, so
`negY 0 0 = −0 − 0 − 0 = 0 = yT`, i.e. `T = −T`, which is `T + T = 0` by
`add_eq_zero_iff_eq_neg`.  This is the `htors` that `weilPairingMu_mulByTwoEndo_of_baseField`
wants, in the `torsionPoint` form it wants it in. -/
private lemma exampleTorsionTwo :
    torsionPoint exampleEquation + torsionPoint exampleEquation = 0 := by
  rw [add_eq_zero_iff_eq_neg]
  simp only [torsionPoint, Point.neg_some, Point.some.injEq]
  norm_num [exampleCurve, WeierstrassCurve.Affine.negY]

open Classical in
/-- The root-of-unity datum at the `[2]∗`-pullback of the constant function `1`.  It is closed
outright by `weilPairingElt_mulByTwoEndo_of_baseField`, so nothing is assumed here. -/
private lemma examplePowMulByTwo :
    weilPairingElt exampleEquation
        (mulByTwoEndo (W := exampleCurve) exampleTwoNeZero 1) ^ 2 = 1 := by
  rw [weilPairingElt_mulByTwoEndo_of_baseField exampleEquation exampleTwoNeZero exampleTorsionTwo
    one_ne_zero, one_pow]

open Classical in
/-- **The `[2]∗` correction factor really does contribute the group identity, on a curve that
exists.**  Every hypothesis of `weilPairingMu_mulByTwoEndo_of_baseField` is discharged: `2 ≠ 0` in
`AlgebraicClosure ℚ`, `T = (0, 0)` is `2`-torsion on `y² = x³ − x`, and `1 ≠ 0` in the function
field.  Nothing is left over. -/
example : weilPairingMu exampleEquation examplePowMulByTwo = 1 :=
  weilPairingMu_mulByTwoEndo_of_baseField exampleEquation exampleTwoNeZero exampleTorsionTwo
    one_ne_zero _

/-! #### The `[3]∗` pullback: a second curve, `y² + y = x³`, on which `T = (0, 0)` has order `3`

The `[3]∗` lemma cannot be certified on `y² = x³ − x` at `T = (0, 0)`: that point has order `2`, so
`weilPairingMu_mulByThreeEndo_of_baseField`'s `htors : T ⊕ T ⊕ T = O` is false there.  The curve
below is `WeilPairingAlternatingThree`'s certificate curve, on which `T = (0, 0)` has order exactly
`3`. -/

private lemma exampleThreeNeZero : (3 : exampleField) ≠ 0 := by norm_num

/-- The curve `y² + y = x³` over `AlgebraicClosure ℚ`, of discriminant `−27`. -/
private noncomputable def exampleCurveThree : Affine exampleField := ⟨0, 0, 1, 0, 0⟩

private instance : exampleCurveThree.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurveThree, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- `T = (0, 0)` lies on `y² + y = x³`. -/
private lemma exampleEquationThree : exampleCurveThree.Equation 0 0 := by
  rw [equation_iff]
  norm_num [exampleCurveThree]

open Classical in
/-- `T = (0, 0)` has order `3` on `y² + y = x³`: it is not fixed by negation
(`negY 0 0 = −1 ≠ 0`) and `Ψ₃ = 3X⁴ + 3b₆X` vanishes at `0`, so
`mem_torsion_three_some_iff` applies; unfolding `(3 : ℕ) • T = 0` gives the three-term relation
that `weilPairingMu_mulByThreeEndo_of_baseField` asks for. -/
private lemma exampleTorsionThree :
    torsionPoint exampleEquationThree + torsionPoint exampleEquationThree
        + torsionPoint exampleEquationThree = 0 := by
  have hn := mem_torsion_iff.mp
    ((mem_torsion_three_some_iff
      (h := exampleCurveThree.equation_iff_nonsingular.mp exampleEquationThree)
      (by norm_num [exampleCurveThree, WeierstrassCurve.Affine.negY])).mpr
      (by norm_num [exampleCurveThree, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂,
        WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]))
  rw [show (3 : ℕ) = 2 + 1 from rfl, add_smul, two_nsmul, one_nsmul] at hn
  exact hn

open Classical in
/-- The root-of-unity datum at the `[3]∗`-pullback of the constant function `1`, closed outright by
`weilPairingElt_mulByThreeEndo_of_baseField`.  The exponent is `3` here, matching the order of the
translation point. -/
private lemma examplePowMulByThree :
    weilPairingElt exampleEquationThree
        (mulByThreeEndo (W := exampleCurveThree) exampleTwoNeZero exampleThreeNeZero 1) ^ 3
      = 1 := by
  rw [weilPairingElt_mulByThreeEndo_of_baseField exampleEquationThree exampleTwoNeZero
    exampleThreeNeZero exampleTorsionThree one_ne_zero, one_pow]

open Classical in
/-- **The `[3]∗` correction factor really does contribute the group identity, on a curve that
exists.**  Every hypothesis of `weilPairingMu_mulByThreeEndo_of_baseField` is discharged: `2 ≠ 0`
and `3 ≠ 0` in `AlgebraicClosure ℚ`, `T = (0, 0)` has order `3` on `y² + y = x³`, and `1 ≠ 0` in
the function field. -/
example : weilPairingMu exampleEquationThree examplePowMulByThree = 1 :=
  weilPairingMu_mulByThreeEndo_of_baseField exampleEquationThree exampleTwoNeZero
    exampleThreeNeZero exampleTorsionThree one_ne_zero _

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
