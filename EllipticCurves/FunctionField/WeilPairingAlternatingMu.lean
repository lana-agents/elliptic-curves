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
root-of-unity data (already delivered).  The single carried input is the translation-invariance
`τ_T∗ g_T = g_T`, taken as an explicit hypothesis exactly as in the `F(W)`-level reduction
(#465, deliverable 2 — the product-over-`⟨T⟩` / divisor-telescoping discharge).  ⚠️ That
parenthesis used to end *"gated on the divisor calculus"*; the discharge has been run at both `n`
over `F̄` (`WeilPairingAlternating{Two,Three}AlgClosed`) and over an arbitrary field with `hprin`
(`WeilPairingAlternatingBaseChange`), so the hypothesis is carried by design and not by blockage.
Antisymmetry (`e_n(T, S) = e_n(S, T)⁻¹`) is *not*
among what remains: it and the divisor-slot bilinearity it runs on are merged at the `F(W)` level
as `WeilPairingAntisymmetric` (#723), and their `μ_n` lift — the same descent performed here — is
merged as `WeilPairingAntisymmetricMu` (#733).  Both need `[Field F] [W.IsElliptic]` and nothing
more, with only the production of `g_{S ⊕ T} = g_S · g_T · w` still carried as a hypothesis
— ⚠️ **rung 5 only, never rung 4**, and performed in `WeilPairingProductRelation` (#845).
The divisor slot is moreover bundled as a homomorphism into `μ_n(F)` in
`WeilPairingDivisorSlotHom` (#746).

⚠️ **This paragraph used to close with a list of what was left at the `μ_n` level, and all three
entries have landed.**  It read *"What remains at the `μ_n` level is Galois-equivariance (`#456`),
the same bundling in the *translation* slot …, and non-degeneracy"*:

* Galois-equivariance in `μ_n(F)` — `exists_weilPairingMu_galois_{two,three}`
  (`EllipticCurves.FunctionField.WeilPairingGaloisRoot`, `#859`), with the two `hpow` produced;
* the translation-slot bundling — `weilPairingTorsionMuHom_{two,three}`
  (`EllipticCurves.FunctionField.WeilPairingTranslationSlotHom`, `#890`).  ⚠️ The parenthesis was
  right about *why* it is a different statement: the datum had to become a **membership**, and
  `weilPairingPointSubgroup` is what makes it one;
* non-degeneracy in `μ_n(F)` — `exists_gS_{two,three}_weilPairingMu_ne_one`
  (`EllipticCurves.FunctionField.WeilPairingNondegenerateMu`, `#878`), over `F̄`.

⚠️ **State the position, never a tally**: what is left over `F̄` is not a shorter list but `hprin`
over a **general** field (`#962`) and general `n` (⚠️ no longer `#251`, which is closed — see
below). Non-degeneracy is still **not** Ward-gated; `WeilPairing`'s scope section is the canonical
account of what it consumes (#769), and over a non-closed field it is not merely unproved — see that
account.

⚠️ **That bullet read *"general `n` (`#404`'s `ωₙ`)"*, then *"general `n` (`#251`)"*, and both of
those are now closed.**  PR #557 proved the on-curve identity for `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` at every index
over every commutative ring — `WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero`,
`EllipticCurves.Torsion.OmegaCrux`.  The *other* statement this tree also called `ωₙ` — the
identification of those coordinates with the **group-law** multiple `n • P` — is `#251` on its
`x`-half and `#1500` on its `y`-half, and **both are closed**: `hasXCoordFormula_of_two_ne_zero`
(`EllipticCurves.Torsion.NsmulOrder`) and `nsmul_eq_some_omegaY_of_ΨSq_ne_zero`
(`EllipticCurves.Torsion.NsmulYPeriodic`, PR #579), each at every index over a field with
`(2 : F) ≠ 0`.  ⚠️ That was the step `hprin` reaches through
`MulByTwoFibreAffine`/`MulByThreeFibre`, whose own input is `addY_self_eq_div`
(`EllipticCurves.Torsion.DoublingCoords`) and its `n = 3` mirror — and that input now exists at
every index.  ⚠️ **Whether it unblocks those two fibre descriptions is NOT measured**, here or
anywhere in this tree: the bullet is retired because the reason it gave is false, not because a
replacement reason was found.  The two-reading account is
`EllipticCurves.FunctionField.MulByNPullback`.

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
the single carried input, and the product-over-`⟨T⟩` argument (#465 deliverable 2) is what supplies
it.

⚠️ *"to be discharged by"* is what this sentence used to say, and it is discharged — at both `n`
over `F̄` in `EllipticCurves.FunctionField.WeilPairingAlternatingTwoAlgClosed` and
`…WeilPairingAlternatingThreeAlgClosed`, and over an arbitrary field with `hprin` in
`…WeilPairingAlternatingBaseChange`, whose `exists_weilPairingMu_self_eq_one_of_hprin_{two,three}`
are the `μ_n(F)` companions of exactly this statement. -/
theorem weilPairingMu_self_of_translateEndo_fixed {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    {g : W.FunctionField} (hg : g ≠ 0) {n : ℕ} [NeZero n]
    (hpow : weilPairingElt h₂ g ^ n = 1) (htinv : translateEndo h₂ g = g) :
    weilPairingMu h₂ hpow = 1 :=
  (weilPairingMu_eq_one_iff_translateEndo_fixed h₂ hg hpow).mpr htinv

end CoordinateRing

end WeierstrassCurve.Affine
