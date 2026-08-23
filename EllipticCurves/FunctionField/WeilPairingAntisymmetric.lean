/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.TranslationDoublingComm
import EllipticCurves.FunctionField.TranslationTorsion
import EllipticCurves.FunctionField.TranslationTriplingComm
import EllipticCurves.FunctionField.WeilPairingAlternating
import EllipticCurves.FunctionField.WeilPairingBilinearBaseField

/-!
# Divisor-slot bilinearity and antisymmetry of the Weil-pairing element (rung 6)

For the divisor-theoretic Weil-pairing element (`WeilPairing.lean`, `#419`)

```
e_n(S, T) := weilPairingElt h_T g_S = τ_T∗(g_S) / g_S,   τ_T∗ = translateEndo h_T,
```

three of the four named structural properties of Silverman *AEC* III.8.1 are merged: bilinearity in
the **translation** slot `T` (`WeilPairingBilinear`, `WeilPairingBilinearBaseField`), constancy
(`WeilPairingConstant`), and — at `n = 2` and `n = 3` over an algebraically closed field — the
alternating property `e_n(T, T) = 1` (`WeilPairingAlternatingTwo`, `WeilPairingAlternatingThree`).

This file supplies the fourth, **antisymmetry** `e_n(T, S) = e_n(S, T)⁻¹`, together with the
bilinearity in the **divisor** slot `S` that it runs on.

## What was deferred, and why the deferral overpriced it

Every file that mentions divisor-slot bilinearity defers it in the same words —
`WeilPairingBilinear`'s scope note says it "needs `g_{S ⊕ S'} = g_S · g_{S'}` up to a constant, a
divisor-level statement gated on rung 4", and `WeilPairingAlternatingThree`'s "Explicitly not here"
list defers antisymmetry to it.

That is right about *what* is missing and wrong about what it costs.  ⚠️ **It is also wrong that
the production of `g_R = g_S · g_T · w` is rung-4 gated**, as this file used to say here: it
follows from rung-5 data alone, by `exists_prod_eq_of_pullback`
(`EllipticCurves.FunctionField.WeilPairingProductRelation`, `#845`), whose divisor input is the
Abel–Jacobi statement that `(S) + (T) − (S ⊕ T)` is principal — available from
`EllipticCurves.FunctionField.DivisorPrincipality` (`#726`) over an arbitrary field.  Everything
that *consumes* `hprod` is ungated too, because the correction factor `w` is invisible to
`e_n(·, T)`:

* `e_n(·, T)` is **multiplicative in the divisor slot on the nose** (`weilPairingElt_mul`) —
  `translateEndo` is a ring hom and `(a·b)/(g₁·g₂) = (a/g₁)·(b/g₂)`.  No hypotheses at all, not even
  nonvanishing;
* a nonzero constant contributes `1` (`weilPairingElt_algebraMap`), since `translateEndo` fixes the
  base field (`translateEndo_algebraMap_base`, `#432`);
* a pullback `[n]∗f` contributes `1` (`weilPairingElt_mulByTwoEndo`,
  `weilPairingElt_mulByThreeEndo`), since `τ_T∗` fixes it whenever `T` is `n`-torsion — which is
  exactly the merged `hcomm` discharge `translateEndo_mulByTwoEndo_apply` (`#164`) /
  `translateEndo_mulByThreeEndo_apply`.

So the classical shape `g_{S⊕T} = c · g_S · g_T · (h ∘ [n])` costs **nothing** downstream, and the
whole chain is one short file carrying `hprod` as its single gated hypothesis — the same
conditional-partial methodology as `hcomm`, `huf`, `hprin`, `hfix`, `hsum` and `htr` elsewhere in
rung 6.

## The derivation, and where the alternating property enters

```
1 = e(h_R, g_R)                                        -- alternating at R
  = e(h_R, g_S) · e(h_R, g_T)                          -- divisor slot at R
  = e(h_S, g_S)·e(h_T, g_S) · e(h_S, g_T)·e(h_T, g_T)  -- translation slot, twice
  = e(h_T, g_S) · e(h_S, g_T)                          -- alternating at S and at T
```

⚠️ **The alternating property is an input at three points, `S`, `T` and `R = S ⊕ T`, not two.**
`e(h_R, g_R) = 1` is a hypothesis, not a conclusion — antisymmetry does not *prove* the alternating
property anywhere, it consumes it.  That is not a defect: `S`, `T` and `S ⊕ T` are all `n`-torsion,
so over an algebraically closed field all three instances come from the same merged theorem
(`exists_weilPairingElt_self_eq_one_of_algClosed`, resp. `_three`), at three different points.

Note also that only **one** of the three needs the divisor-slot step, so only `e_n(h_R, w) = 1` is
required of the correction factor; `e_n(h_S, w)` and `e_n(h_T, w)` never appear.

## Main results

* `weilPairingElt_mul` — `e(g₁ · g₂) = e(g₁) · e(g₂)`, unconditional;
* `weilPairingElt_algebraMap`, `weilPairingElt_mulByTwoEndo`, `weilPairingElt_mulByThreeEndo` and
  their base-field (`torsionPoint`) forms — the correction factors contribute `1`;
* **`weilPairingElt_divisorSlot_add`** — divisor-slot bilinearity from `hprod` and `e_n(w) = 1`,
  with the concrete `n = 2` / `n = 3` corollaries `_two` / `_three` in which `w` is
  `c · [n]∗f` and the second hypothesis is discharged outright;
* **`weilPairingElt_mul_swap_eq_one`** — antisymmetry in product form
  `e_n(S, T) · e_n(T, S) = 1`;
* **`weilPairingElt_eq_inv`** — the quotable form `e_n(T, S) = (e_n(S, T))⁻¹`.

## Scope

`[Field F] {W : Affine F} [W.IsElliptic]` throughout.  **No `[IsDedekindDomain W.CoordinateRing]`,
no `[IsAlgClosed F]`, no `#418`, no rung 4** — if any of those were needed the conditional-partial
boundary would be drawn in the wrong place, since the gated content is exactly `hprod` and nothing
else.  Non-degeneracy stays out, and it is **not** Ward-gated — `WeilPairing`'s scope section is
the canonical account of what it consumes (`#769`).

## Non-vacuity

The first group of results is unconditional, so vacuity is not a question for them; `_two` /
`_three` and `_const` exhibit correction factors `w` for which the second hypothesis of
`weilPairingElt_divisorSlot_add` is *proved* rather than assumed, so that theorem has content
beyond `w = 1`.  The antisymmetry headline is not instantiated outright **here**, because `hprod`
is a hypothesis of it.  ⚠️ That is a fact about this file only: `hprod` is produced from rung-5
data by `exists_prod_eq_of_pullback`, and the whole headline is instantiated unconditionally over
`F̄` at `n = 2` and `n = 3` in `EllipticCurves.FunctionField.WeilPairingProductRelation` (`#845`),
where it is certified on named torsion points.  Every hypothesis this file adds on top of `hprod`
is discharged here or merged.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(a) (bilinearity) and
  III.8.1(d) (alternating, hence antisymmetric).
-/

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-! ### Multiplicativity in the divisor slot -/

/-- **`e_n(·, T)` is multiplicative in the divisor slot, on the nose.**

```
e_n(g₁ · g₂, T) = e_n(g₁, T) · e_n(g₂, T)
```

`translateEndo h₂` is a ring homomorphism and `(a · b) / (g₁ · g₂) = (a / g₁) · (b / g₂)` in a
field, so this needs no hypotheses whatsoever — not even `g₁, g₂ ≠ 0`, the degenerate cases being
`0 = 0`.  It is the engine behind divisor-slot bilinearity: once the product relation
`g_{S ⊕ T} = g_S · g_T · w` is granted, all that remains is to show the correction factor `w`
contributes `1`. -/
theorem weilPairingElt_mul {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) (g₁ g₂ : W.FunctionField) :
    weilPairingElt h₂ (g₁ * g₂) = weilPairingElt h₂ g₁ * weilPairingElt h₂ g₂ := by
  simp only [weilPairingElt, map_mul]
  exact (div_mul_div_comm _ _ _ _).symm

/-- **`e_n(g⁻¹, T) = e_n(g, T)⁻¹`** — the divisor slot is multiplicative for inverses too.  Recorded
because the antisymmetry corollary is naturally stated with an inverse on one side. -/
theorem weilPairingElt_inv {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) (g : W.FunctionField) :
    weilPairingElt h₂ g⁻¹ = (weilPairingElt h₂ g)⁻¹ := by
  simp only [weilPairingElt, map_inv₀, inv_div_inv, inv_div]

/-! ### The correction factors contribute `1` -/

/-- **A nonzero constant contributes `1`.**  `translateEndo` fixes the base field
(`translateEndo_algebraMap_base`, `#432`), so `e_n(algebraMap c, T) = c / c = 1`. -/
theorem weilPairingElt_algebraMap {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {c : F} (hc : c ≠ 0) :
    weilPairingElt h₂ (algebraMap F W.FunctionField c) = 1 :=
  (weilPairingElt_eq_one_iff_translateEndo_fixed h₂
    ((map_ne_zero_iff _ (algebraMap F W.FunctionField).injective).mpr hc)).mpr
      (translateEndo_algebraMap_base h₂ c)

variable {xT yT : F}

/-- **A `[2]∗`-pullback contributes `1`, for a `2`-torsion translation point.**  The merged `hcomm`
discharge `translateEndo_mulByTwoEndo_apply` (`#164`) says `τ_T∗` fixes `[2]∗f` outright whenever
`𝒯_T + 𝒯_T = 0`, and a fixed nonzero element has pairing value `1`. -/
theorem weilPairingElt_mulByTwoEndo (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0)
    (htors : translatePoint hT + translatePoint hT = 0) {f : W.FunctionField} (hf : f ≠ 0) :
    weilPairingElt hT (mulByTwoEndo h2 f) = 1 :=
  (weilPairingElt_eq_one_iff_translateEndo_fixed hT
    (fun hz => hf ((mulByTwoEndo h2).injective (by rw [hz, map_zero])))).mpr
      (translateEndo_mulByTwoEndo_apply hT h2 htors f)

open Classical in
/-- **A `[2]∗`-pullback contributes `1`, from the base-field `2`-torsion of `T`.**  The
`torsionPoint` form of `weilPairingElt_mulByTwoEndo`, transporting `T + T = 0` in `W.Point` through
`translatePoint_add_self` (`#166`). -/
theorem weilPairingElt_mulByTwoEndo_of_baseField (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0)
    (htors : torsionPoint hT + torsionPoint hT = 0) {f : W.FunctionField} (hf : f ≠ 0) :
    weilPairingElt hT (mulByTwoEndo h2 f) = 1 :=
  weilPairingElt_mulByTwoEndo hT h2 (translatePoint_add_self hT htors) hf

/-- **A `[3]∗`-pullback contributes `1`, for a `3`-torsion translation point.**  The `n = 3` mirror
of `weilPairingElt_mulByTwoEndo`, off `translateEndo_mulByThreeEndo_apply`. -/
theorem weilPairingElt_mulByThreeEndo (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (htors : translatePoint hT + translatePoint hT + translatePoint hT = 0)
    {f : W.FunctionField} (hf : f ≠ 0) :
    weilPairingElt hT (mulByThreeEndo h2 h3 f) = 1 :=
  (weilPairingElt_eq_one_iff_translateEndo_fixed hT
    (fun hz => hf ((mulByThreeEndo h2 h3).injective (by rw [hz, map_zero])))).mpr
      (translateEndo_mulByThreeEndo_apply hT h2 h3 htors f)

open Classical in
/-- **A `[3]∗`-pullback contributes `1`, from the base-field `3`-torsion of `T`.**  The
`torsionPoint` form of `weilPairingElt_mulByThreeEndo`, via `translatePoint_add_add_self`
(`#444`). -/
theorem weilPairingElt_mulByThreeEndo_of_baseField (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0)
    (htors : torsionPoint hT + torsionPoint hT + torsionPoint hT = 0)
    {f : W.FunctionField} (hf : f ≠ 0) :
    weilPairingElt hT (mulByThreeEndo h2 h3 f) = 1 :=
  weilPairingElt_mulByThreeEndo hT h2 h3 (translatePoint_add_add_self hT htors) hf

/-! ### Bilinearity in the divisor slot -/

/-- **Bilinearity of the Weil-pairing element in the divisor slot.**  Given the product
relation

```
hprod : g_R = g_S · g_T · w        (for  S ⊕ T = R)
```

and that the correction factor is invisible to the pairing (`hw : e_n(w, T) = 1`),

```
e_n(g_R, T) = e_n(g_S, T) · e_n(g_T, T).
```

The whole proof is `weilPairingElt_mul` twice; `hprod` is the single carried input and is **not**
produced here — it is produced from rung-5 data in
`EllipticCurves.FunctionField.WeilPairingProductRelation` (`#845`), and ⚠️ needs no rung 4.  The
two hypotheses are independent: `hprod` is about the roots, `hw` about the translation point, and
the concrete corollaries below discharge `hw`. -/
theorem weilPairingElt_divisorSlot_add {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    {gS gT gR w : W.FunctionField} (hprod : gR = gS * gT * w)
    (hw : weilPairingElt h₂ w = 1) :
    weilPairingElt h₂ gR = weilPairingElt h₂ gS * weilPairingElt h₂ gT := by
  rw [hprod, weilPairingElt_mul, weilPairingElt_mul, hw, mul_one]

/-- **Divisor-slot bilinearity when the correction factor is a nonzero constant.**  The cheapest
non-trivial instance of `weilPairingElt_divisorSlot_add`: `hw` is `weilPairingElt_algebraMap`, and
no torsion hypothesis on the translation point is needed. -/
theorem weilPairingElt_divisorSlot_add_const {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    {gS gT gR : W.FunctionField} {c : F} (hc : c ≠ 0)
    (hprod : gR = gS * gT * algebraMap F W.FunctionField c) :
    weilPairingElt h₂ gR = weilPairingElt h₂ gS * weilPairingElt h₂ gT :=
  weilPairingElt_divisorSlot_add h₂ hprod (weilPairingElt_algebraMap h₂ hc)

open Classical in
/-- **Divisor-slot bilinearity at `n = 2`, with the classical correction factor.**  Here
`w = c · [2]∗f` is exactly the shape Silverman's `g_{S ⊕ T} = c · g_S · g_T · (h ∘ [2])` produces,
and `hw` is discharged by `weilPairingElt_algebraMap` and `weilPairingElt_mulByTwoEndo`. -/
theorem weilPairingElt_divisorSlot_add_two (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0)
    (htors : torsionPoint hT + torsionPoint hT = 0)
    {gS gT gR f : W.FunctionField} {c : F} (hc : c ≠ 0) (hf : f ≠ 0)
    (hprod : gR = gS * gT * (algebraMap F W.FunctionField c * mulByTwoEndo h2 f)) :
    weilPairingElt hT gR = weilPairingElt hT gS * weilPairingElt hT gT :=
  weilPairingElt_divisorSlot_add hT hprod <| by
    rw [weilPairingElt_mul, weilPairingElt_algebraMap hT hc,
      weilPairingElt_mulByTwoEndo_of_baseField hT h2 htors hf, mul_one]

open Classical in
/-- **Divisor-slot bilinearity at `n = 3`, with the classical correction factor.**  The
`mulByThreeEndo` mirror of `weilPairingElt_divisorSlot_add_two`. -/
theorem weilPairingElt_divisorSlot_add_three (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (htors : torsionPoint hT + torsionPoint hT + torsionPoint hT = 0)
    {gS gT gR f : W.FunctionField} {c : F} (hc : c ≠ 0) (hf : f ≠ 0)
    (hprod : gR = gS * gT * (algebraMap F W.FunctionField c * mulByThreeEndo h2 h3 f)) :
    weilPairingElt hT gR = weilPairingElt hT gS * weilPairingElt hT gT :=
  weilPairingElt_divisorSlot_add hT hprod <| by
    rw [weilPairingElt_mul, weilPairingElt_algebraMap hT hc,
      weilPairingElt_mulByThreeEndo_of_baseField hT h2 h3 htors hf, mul_one]

/-! ### Antisymmetry -/

open Classical in
/-- **Antisymmetry of the Weil-pairing element, in product form.**

```
e_n(S, T) · e_n(T, S) = 1.
```

The inputs, in the order the proof uses them:

* `hadd` — the base-field group relation `S ⊕ T = R` (transported to `F(W)` internally by
  `translatePoint_add`, `#460`);
* `hprod`/`hwR` — the divisor-slot datum at `R` only.  `e_n(w, S)` and `e_n(w, T)` are never needed;
* `hpow` — the root-of-unity datum `e_n(g_S, T) ^ n = 1` that the merged translation-slot
  bilinearity `weilPairingElt_translatePoint_add_of_baseField` consumes.  The companion datum for
  `g_T` is free, since `haltT` already says the value is `1`;
* `haltS`, `haltT`, `haltR` — the **alternating property at `S`, at `T` and at `R`**.  All three are
  hypotheses; see the module docstring.

Over an algebraically closed field the three alternating inputs come from a single merged theorem
applied at three points, so this is not three separate gates. -/
theorem weilPairingElt_mul_swap_eq_one {xS yS xR yR : F}
    (hS : W.Equation xS yS) (hT : W.Equation xT yT) (hR : W.Equation xR yR)
    (hadd : torsionPoint hS + torsionPoint hT = torsionPoint hR)
    {gS gT gR w : W.FunctionField} (hgS : gS ≠ 0) (hgT : gT ≠ 0)
    (hprod : gR = gS * gT * w) (hwR : weilPairingElt hR w = 1)
    {n : ℕ} (hn : n ≠ 0) (hpow : weilPairingElt hT gS ^ n = 1)
    (haltS : weilPairingElt hS gS = 1) (haltT : weilPairingElt hT gT = 1)
    (haltR : weilPairingElt hR gR = 1) :
    weilPairingElt hS gT * weilPairingElt hT gS = 1 := by
  have hbS : weilPairingElt hR gS = weilPairingElt hS gS * weilPairingElt hT gS :=
    weilPairingElt_translatePoint_add_of_baseField hS hT hR hadd hgS hn hpow
  have hbT : weilPairingElt hR gT = weilPairingElt hS gT * weilPairingElt hT gT :=
    weilPairingElt_translatePoint_add_of_baseField hS hT hR hadd hgT hn
      (by rw [haltT, one_pow])
  have hd : weilPairingElt hR gR = weilPairingElt hR gS * weilPairingElt hR gT :=
    weilPairingElt_divisorSlot_add hR hprod hwR
  rw [hd, hbS, hbT, haltS, haltT, one_mul, mul_one] at haltR
  rw [mul_comm]
  exact haltR

open Classical in
/-- **Antisymmetry, in the quotable inverse form** `e_n(T, S) = e_n(S, T)⁻¹`.  Immediate from
`weilPairingElt_mul_swap_eq_one`; no nonvanishing hypothesis is needed, since `a * b = 1` already
forces `a = b⁻¹` in a field. -/
theorem weilPairingElt_eq_inv {xS yS xR yR : F}
    (hS : W.Equation xS yS) (hT : W.Equation xT yT) (hR : W.Equation xR yR)
    (hadd : torsionPoint hS + torsionPoint hT = torsionPoint hR)
    {gS gT gR w : W.FunctionField} (hgS : gS ≠ 0) (hgT : gT ≠ 0)
    (hprod : gR = gS * gT * w) (hwR : weilPairingElt hR w = 1)
    {n : ℕ} (hn : n ≠ 0) (hpow : weilPairingElt hT gS ^ n = 1)
    (haltS : weilPairingElt hS gS = 1) (haltT : weilPairingElt hT gT = 1)
    (haltR : weilPairingElt hR gR = 1) :
    weilPairingElt hS gT = (weilPairingElt hT gS)⁻¹ :=
  eq_inv_of_mul_eq_one_left
    (weilPairingElt_mul_swap_eq_one hS hT hR hadd hgS hgT hprod hwR hn hpow haltS haltT haltR)

end CoordinateRing

end WeierstrassCurve.Affine
