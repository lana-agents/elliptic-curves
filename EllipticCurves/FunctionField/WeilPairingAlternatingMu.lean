/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairingAlternating
import EllipticCurves.FunctionField.WeilPairingBilinearMu

/-!
# The alternating property `e_n(T, T) = 1` at the `μ_n(F)` group level (rung 6)

Let `W` be an elliptic curve over a field `F`.  The alternating property of the divisor-theoretic
Weil-pairing element (`WeilPairing.lean`, issue #419)

```
e_n(S, T) := weilPairingElt h₂ g = τ_T∗(g) / g,   τ_T∗ = translateEndo h₂ : F(W) →+* F(W),
```

is delivered as the Ward- and normality-independent *reduction*
`weilPairingElt_eq_one_iff_translateEndo_fixed` (`WeilPairingAlternating.lean`, #465): for
`g ≠ 0`,

```
e_n(T, T) = 1   ⟺   τ_T∗ g_T = g_T   in F(W).
```

That statement lives in the function field `F(W)`.  This file lifts it to a genuine **group
equation** in `μ_n(F) = rootsOfUnity n F ≤ Fˣ`, the honest value group of the Weil pairing
(Silverman AEC III.8): writing `weilPairingMu` (`WeilPairingRootsOfUnity.lean`, #457) for the
pairing value packaged as an element of `μ_n(F)`,

```
weilPairingMu(T, T) = 1   in μ_n(F)   ⟺   τ_T∗ g_T = g_T,
```

so the alternating property becomes the assertion that the pairing value is the **group
identity** of `μ_n(F)`.  This is the alternating-property analogue of the translation-slot
multiplicativity lift `weilPairingMu_translatePoint_add_of_baseField`
(`WeilPairingBilinearMu.lean`, #459); together they are the group-level structure of `e_n` in
the value group `μ_n(F)`.

## The route — descend to the base field through the defining property

`weilPairingMu` is an element of the subgroup `rootsOfUnity n F ≤ Fˣ`, so an equation between it
and the group identity `1` is compared after the injective composite
`ζ ↦ algebraMap F F(W) ((ζ : Fˣ) : F)` (`algebraMap_coe_rootsOfUnity_injective`, #459).  Under
it the identity `1 : rootsOfUnity n F` maps to `algebraMap F F(W) 1 = 1`, and `weilPairingMu`
maps back to its `weilPairingElt` via `algebraMap_coe_weilPairingMu` (#457); the equation in
`F(W)` is then exactly the merged reduction
`weilPairingElt_eq_one_iff_translateEndo_fixed` (#465).

## Main results

* `weilPairingMu_eq_one_iff_translateEndo_fixed` — the group-level characterisation
  `weilPairingMu(T, T) = 1 ↔ τ_T∗ g_T = g_T`;
* `weilPairingMu_self_of_translateEndo_fixed` — its forward direction, the reduction
  `τ_T∗ g_T = g_T ⟹ weilPairingMu(T, T) = 1`.

## Scope

Ward-, normality- and rung-4-independent: needs only `[Field F] [W.IsElliptic]` and the
root-of-unity data (already delivered).  The single genuinely-gated input remains the
translation-invariance `τ_T∗ g_T = g_T`, carried as an explicit hypothesis exactly as in the
`F(W)`-level reduction (#465, deliverable 2 — the product-over-`⟨T⟩` / divisor-telescoping
discharge, gated on the divisor calculus).  Antisymmetry (`e_n(T, S) = e_n(S, T)⁻¹`) is *not*
among what remains: it and the divisor-slot bilinearity it runs on are merged at the `F(W)` level
as `WeilPairingAntisymmetric` (#723), and their `μ_n` lift — the same descent performed here — is
merged as `WeilPairingAntisymmetricMu` (#733).  Both need `[Field F] [W.IsElliptic]` and nothing
more, with only the production of `g_{S ⊕ T} = g_S · g_T · w` still carried as a hypothesis
— ⚠️ **rung 5 only, never rung 4**, and performed in `WeilPairingProductRelation` (#845).
The divisor slot is moreover bundled as a homomorphism into `μ_n(F)` in
`WeilPairingDivisorSlotHom` (#746).  What remains at the `μ_n` level is Galois-equivariance
(#456), the same bundling in the *translation* slot (which needs a datum uniform in the
translation point, a genuinely different statement), and non-degeneracy — which is **not**
Ward-gated; `WeilPairing`'s scope section is the canonical account of what it consumes (#769).

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.
-/

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-- **The alternating property at the `μ_n(F)` group level is exactly translation-invariance of
`g_T`.**  For `g_T ≠ 0` the `μ_n(F)`-packaged Weil-pairing element `weilPairingMu(T, T)` is the
group identity `1` if and only if the translation `τ_T∗` fixes `g_T`:

```
weilPairingMu h₂ hpow = 1 ↔ translateEndo h₂ g = g.
```

The group-level form of `weilPairingElt_eq_one_iff_translateEndo_fixed` (#465): both directions are
pushed, through the injective composite `ζ ↦ algebraMap F F(W) ((ζ : Fˣ) : F)`
(`algebraMap_coe_rootsOfUnity_injective`), to the `F(W)`-level reduction, using that
`1 : rootsOfUnity n F` maps to `1`. -/
theorem weilPairingMu_eq_one_iff_translateEndo_fixed {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    {g : W.FunctionField} (hg : g ≠ 0) {n : ℕ} [NeZero n]
    (hpow : weilPairingElt h₂ g ^ n = 1) :
    weilPairingMu h₂ hpow = 1 ↔ translateEndo h₂ g = g := by
  rw [← weilPairingElt_eq_one_iff_translateEndo_fixed h₂ hg]
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

/-- **The alternating property at the `μ_n(F)` group level (`weilPairingMu(T, T) = 1`).**  If the
translation `τ_T∗` fixes the rung-5 root `g_T` (`htinv : translateEndo h₂ g = g`), then the
`μ_n(F)`-packaged Weil-pairing element `weilPairingMu(T, T)` is the group identity `1`.

The forward direction of `weilPairingMu_eq_one_iff_translateEndo_fixed`; the hypothesis `htinv` is
the single genuinely-gated input, to be discharged by the product-over-`⟨T⟩` argument
(#465 deliverable 2). -/
theorem weilPairingMu_self_of_translateEndo_fixed {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    {g : W.FunctionField} (hg : g ≠ 0) {n : ℕ} [NeZero n]
    (hpow : weilPairingElt h₂ g ^ n = 1) (htinv : translateEndo h₂ g = g) :
    weilPairingMu h₂ hpow = 1 :=
  (weilPairingMu_eq_one_iff_translateEndo_fixed h₂ hg hpow).mpr htinv

end CoordinateRing

end WeierstrassCurve.Affine
