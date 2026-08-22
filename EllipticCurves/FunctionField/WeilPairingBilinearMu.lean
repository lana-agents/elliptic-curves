/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairingBilinearBaseField
import EllipticCurves.FunctionField.WeilPairingRootsOfUnity

/-!
# Translation-slot multiplicativity of `e_n` at the `μ_n(F)` group level (rung 6)

Let `W` be an elliptic curve over a field `F`.  The translation-slot bilinearity of the
Weil-pairing element (`WeilPairing.lean`, issue #419)

```
e_n(S, T) := weilPairingElt h₂ g = τ_T∗(g) / g,   τ_T∗ = translateEndo h₂ : F(W) →+* F(W),
```

is delivered — from an honest base-field group relation — as
`weilPairingElt_translatePoint_add_of_baseField` (`WeilPairingBilinearBaseField.lean`, #451): for
base-field points `P, Q, R` on `W` with `P ⊕ Q = R` in `W.Point`,

```
e_n(S, T_R) = e_n(S, T_P) · e_n(S, T_Q)   in F(W).
```

That identity lives in the function field `F(W)`.  This file lifts it to a genuine **group
equation** in `μ_n(F) = rootsOfUnity n F ≤ Fˣ`, the honest value group of the Weil pairing
(Silverman AEC III.8): writing `weilPairingMu` (`WeilPairingRootsOfUnity.lean`, #457) for the
pairing value packaged as an element of `μ_n(F)`,

```
weilPairingMu(S, T_R) = weilPairingMu(S, T_P) · weilPairingMu(S, T_Q)   in μ_n(F).
```

This is the group-level statement of translation-slot multiplicativity — the step towards `e_n`
assembled as a `μ_n`-valued group homomorphism in the translation slot.

## The route — descend to the base field through the defining property

`weilPairingMu` is an element of the subgroup `rootsOfUnity n F ≤ Fˣ`, so the two sides are compared
after the injective composite `ζ ↦ algebraMap F F(W) ((ζ : Fˣ) : F)` (`algebraMap F F(W)` is
injective as `F(W)` is a fraction field; `Units.val` and the subgroup-subtype coercion are
injective).  On the underlying `F(W)` values, `algebraMap_coe_weilPairingMu` (#457) turns each
`weilPairingMu` back into its `weilPairingElt`, the product distributes through `Subgroup.coe_mul`
/ `Units.val_mul` /
`map_mul`, and the landed base-field bilinearity `weilPairingElt_translatePoint_add_of_baseField`
closes it.

## Main result

* `weilPairingMu_translatePoint_add_of_baseField` — multiplicativity of `weilPairingMu` in the
  translation slot, in the group `rootsOfUnity n F`, from the base-field relation
  `torsionPoint hP + torsionPoint hQ = torsionPoint hR`.

## Scope

Ward-, normality- and rung-4-independent: needs only `[Field F] [W.IsElliptic]` and the already
delivered root-of-unity data.  Bilinearity in the divisor slot `S` and antisymmetry are merged at
the `F(W)` level (`WeilPairingAntisymmetric`, #723) on the same `[Field F] [W.IsElliptic]`, with
only the production of `g_{S ⊕ S'} = g_S · g_{S'} · w` still carried as a hypothesis (rung 4/5,
#414/#418); their `μ_n` lift is merged as `WeilPairingAntisymmetricMu` (#733), by the same descent
through `algebraMap_coe_rootsOfUnity_injective` used below.  Alternating `e_n(S, S) = 1` and
Galois-equivariance remain separate/gated #419 sub-items; non-degeneracy is Ward-gated (#242).

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.
-/

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

omit [W.IsElliptic] in
/-- The composite `rootsOfUnity n F → F(W)`, `ζ ↦ algebraMap F F(W) ((ζ : Fˣ) : F)`, is injective:
`algebraMap F F(W)` is injective (`F(W)` is a fraction field of an integral domain), and both the
`Fˣ → F` coercion and the subgroup-subtype coercion `rootsOfUnity n F → Fˣ` are injective. -/
theorem algebraMap_coe_rootsOfUnity_injective {n : ℕ} :
    Function.Injective
      (fun ζ : rootsOfUnity n F => algebraMap F W.FunctionField ((ζ : Fˣ) : F)) := fun _ _ hab =>
  Subtype.ext (Units.ext ((algebraMap F W.FunctionField).injective hab))

open Classical in
/-- **Translation-slot multiplicativity of the Weil-pairing element in `μ_n(F)`.**  For base-field
points `P, Q, R` on `W` satisfying `P ⊕ Q = R` in `W.Point` (`hadd`, stated on `torsionPoint`), a
nonzero `g`, `[NeZero n]`, and the root-of-unity data `e_n(S, T_P) ^ n = 1`, `e_n(S, T_Q) ^ n = 1`,
`e_n(S, T_R) ^ n = 1`,

```
weilPairingMu hR hpowR = weilPairingMu hP hpowP · weilPairingMu hQ hpowQ   in rootsOfUnity n F.
```

The group-level form of `weilPairingElt_translatePoint_add_of_baseField` (#451): comparison in the
subgroup `rootsOfUnity n F ≤ Fˣ` is pushed, through the injective composite
`ζ ↦ algebraMap F F(W) ((ζ : Fˣ) : F)` (`algebraMap_coe_rootsOfUnity_injective`), to an equation of
`weilPairingElt`s in `F(W)`, which the base-field bilinearity supplies. -/
theorem weilPairingMu_translatePoint_add_of_baseField
    {xP yP xQ yQ xR yR : F} (hP : W.Equation xP yP) (hQ : W.Equation xQ yQ)
    (hR : W.Equation xR yR)
    (hadd : torsionPoint hP + torsionPoint hQ = torsionPoint hR)
    {g : W.FunctionField} (hg : g ≠ 0) {n : ℕ} [NeZero n]
    (hpowP : weilPairingElt hP g ^ n = 1) (hpowQ : weilPairingElt hQ g ^ n = 1)
    (hpowR : weilPairingElt hR g ^ n = 1) :
    weilPairingMu hR hpowR = weilPairingMu hP hpowP * weilPairingMu hQ hpowQ := by
  have hbil : weilPairingElt hR g = weilPairingElt hP g * weilPairingElt hQ g :=
    weilPairingElt_translatePoint_add_of_baseField hP hQ hR hadd hg (NeZero.ne n) hpowQ
  refine algebraMap_coe_rootsOfUnity_injective (W := W) ?_
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul, algebraMap_coe_weilPairingMu]
  exact hbil

end CoordinateRing

end WeierstrassCurve.Affine
