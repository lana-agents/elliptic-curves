/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairingBilinearMu
import EllipticCurves.FunctionField.WeilPairingGalois

/-!
# Galois-equivariance of the Weil-pairing element at the `μ_n(F)` group level (rung 6)

Let `W` be an elliptic curve over a field `S`, let `F` be a field extension of `S`, and let
`σ : F ≃ₐ[S] F` be an `S`-algebra automorphism of `F`.  Working over the base-changed curve
`W⁄F : Affine F`, the divisor-theoretic Weil-pairing element (`WeilPairing.lean`, issue #419) is
`e_n(S, T) := weilPairingElt h_T g_S = τ_T∗(g_S) / g_S ∈ F(W⁄F)`, and its
**Galois-equivariance** is delivered — in the conditional form sanctioned by #456 — as

```
weilPairingElt_galois_of_transport :
  galoisFunctionField σ (weilPairingElt h₂ g) = weilPairingElt (equation_algEquiv σ h₂) g'
```

from the transport hypothesis `htr : galoisFunctionField σ g = u • g'` (`WeilPairingGalois.lean`,
#456).  That statement lives in the function field `F(W⁄F)`.  This file lifts it to a genuine
**group equation in `μ_n(F) = rootsOfUnity n F ≤ Fˣ`**, the honest value group of the Weil pairing
(Silverman AEC III.8): writing `weilPairingMu` (`WeilPairingRootsOfUnity.lean`, #457) for the
pairing value packaged as an element of `μ_n(F)` and `restrictRootsOfUnity` (Mathlib) for the
`σ`-action on `μ_n(F)`,

```
σ · weilPairingMu(S, T) = weilPairingMu(σS, σT)   in μ_n(F).
```

This is the Galois-equivariance analogue of the `μ_n(F)` group-level lifts already delivered:
translation-slot multiplicativity `weilPairingMu_translatePoint_add_of_baseField`
(`WeilPairingBilinearMu.lean`, #459), the alternating property
`weilPairingMu_self_of_translateEndo_fixed` (`WeilPairingAlternatingMu.lean`, #465), and
divisor-slot bilinearity with antisymmetry, `weilPairingMu_divisorSlot_add` and
`weilPairingMu_eq_inv` (`WeilPairingAntisymmetricMu.lean`, #733); together they are the group-level
structure of `e_n` in the value group `μ_n(F)`.

## The route — descend to the base field through the defining property

Both sides are elements of the subgroup `rootsOfUnity n F ≤ Fˣ`, so an equation between them is
compared after the injective composite `ζ ↦ algebraMap F F(W⁄F) ((ζ : Fˣ) : F)`
(`algebraMap_coe_rootsOfUnity_injective`, #459).  Under it:

* the right-hand side maps to `weilPairingElt (equation_algEquiv σ h₂) g'`
  (`algebraMap_coe_weilPairingMu`, #457);
* the left-hand side maps to `algebraMap F F(W⁄F) (σ c)`, `c = ((weilPairingMu h₂ hpow : Fˣ) : F)`
  (via `restrictRootsOfUnity_coe_apply` + `Units.coe_map`), which is
  `galoisFunctionField σ (algebraMap F F(W⁄F) c)` by the σ-semilinearity on constants
  `galoisFunctionField_algebraMap` (#455), i.e. `galoisFunctionField σ (weilPairingElt h₂ g)`.

The two sides then coincide by the merged `weilPairingElt_galois_of_transport` (#456).  The
statement is `n`-agnostic: the multiplication-by-`n` structure of `g` is absorbed into `htr`, so
there is no `n = 2` / `n = 3` split.

⚠️ **That last step is bound as a hypothesis in its own lemma** rather than left as an `exact`:
`weilPairingMu_galois_of_weilPairingElt` states the descent with the `F(W⁄F)`-level conclusion as
an argument, and `weilPairingMu_galois_of_transport` applies it.  A consumer holding only that
conclusion — because an existential envelope quantified the transport datum away — uses the descent
directly (`#868`).

## Main results

* **`weilPairingMu_galois_of_weilPairingElt`** — the *descent*: it takes the `F(W⁄F)`-level
  conclusion as a hypothesis and pushes it into `μ_n(F)`, for arbitrary `n` and with nothing about
  `divisor g`.  ⚠️ It is stated immediately before the theorem it generalises, and that theorem is
  a one-line application of it (`#868`);
* `weilPairingMu_galois_of_transport` — the conditional group-level Galois-equivariance
  `σ · weilPairingMu(S, T) = weilPairingMu(σS, σT)` from the transport hypothesis;
* `weilPairingMu_galois_of_transport_eq` — the exact-transport (`u = 1`) special case.

## Scope

Ward-, normality- and rung-4-independent.  The `g_S` transport `σ⋆ g_S = u · g_{σS}` is carried
as the explicit hypothesis `htr`, exactly as at the `F(W⁄F)` level.  Its unconditional discharge —
deliverable 2 of #456, and **not** rung-4-gated — is
`EllipticCurves.FunctionField.WeilPairingGaloisRoot`, which states the discharged form at this
level too, so a consumer in `μ_n(F)` need not descend.  ⚠️ Over an algebraically closed base field
that file now also carries `exists_weilPairingMu_galois_two` / `_three` (#859), which need **no**
rung-5 data and no `hpow` proof — only that the two points are `n`-torsion — so a consumer with a
torsion point should reach for those rather than for `weilPairingMu_galois_of_transport` below.
⚠️ Their route is not `weilPairingMu_galois_of_transport` but the descent
`weilPairingMu_galois_of_weilPairingElt` (#859), which is that theorem with the final
`exact weilPairingElt_galois_of_transport σ h₂ htr` replaced by a hypothesis; applying the
conditional statement would mean re-supplying the rung-5 data the unconditional `F(W⁄F)` theorem
has already consumed.  ⚠️ **The descent is stated in this file** — it was originally written into
`…WeilPairingGaloisRoot` alongside its first consumer, which duplicated the proof body across an
import edge, and `#868` moved it here next to the theorem it generalises.

Non-degeneracy stays out, and it is **not** Ward-gated — `WeilPairing`'s scope section is the
canonical account of what it consumes (#769).

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.
-/

namespace WeierstrassCurve.Affine.CoordinateRing

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S} [W.IsElliptic]
  {x₂ y₂ : F}

open Classical in
/-- **Galois-equivariance descends from `F(W⁄F)` to `μ_n(F)`.**

```
σ⋆(e_n(S, T)) = e_n(σS, σT)  in F(W⁄F)   →   σ · μ_n(S, T) = μ_n(σS, σT)  in rootsOfUnity n F.
```

⚠️ **The descent, stated before the theorem it generalises.**
`weilPairingMu_galois_of_transport` below is this lemma applied to
`weilPairingElt_galois_of_transport` (`#456`) and nothing else, so the transport datum `htr` — and
with it every rung-5 input behind it — collapses here to the single conclusion `hgal` it was only
ever used to produce.  Arbitrary `n`, no `[IsAlgClosed F]`, no torsion hypothesis, nothing about
`divisor g`.

⚠️ **The recipe** (`#868`): when a `μ_n(F)` theorem's proof ends in a single
`exact <the F(W⁄F)-level theorem> <args>`, replacing that `exact` by a hypothesis gives a strict
generalisation whose hypotheses are a subset of the original's.  Reach for it whenever a consumer
holds the `F(W⁄F)`-level conclusion but not the data that produced it — typically because an
existential envelope quantified that data away, which is exactly the situation in
`EllipticCurves.FunctionField.WeilPairingGaloisRoot`'s unconditional headlines.  The same move is
recorded in `…WeilPairingAntisymmetricMu` at two further slots.

The route is the injective composite `ζ ↦ algebraMap F F(W⁄F) ((ζ : Fˣ) : F)`
(`algebraMap_coe_rootsOfUnity_injective`, `#459`) together with the defining property
`algebraMap_coe_weilPairingMu` (`#457`) and the σ-semilinearity on constants
`galoisFunctionField_algebraMap` (`#455`). -/
theorem weilPairingMu_galois_of_weilPairingElt (σ : F ≃ₐ[S] F) (h₂ : (W⁄F).Equation x₂ y₂)
    {g g' : (W⁄F).FunctionField} {n : ℕ} [NeZero n]
    (hgal : galoisFunctionField σ (weilPairingElt h₂ g)
      = weilPairingElt (equation_algEquiv σ h₂) g')
    (hpow : weilPairingElt h₂ g ^ n = 1)
    (hpow' : weilPairingElt (equation_algEquiv σ h₂) g' ^ n = 1) :
    restrictRootsOfUnity (σ.toRingEquiv.toRingHom) n (weilPairingMu h₂ hpow)
      = weilPairingMu (equation_algEquiv σ h₂) hpow' := by
  refine algebraMap_coe_rootsOfUnity_injective (W := W⁄F) ?_
  have hcoe :
      ((restrictRootsOfUnity (σ.toRingEquiv.toRingHom) n (weilPairingMu h₂ hpow) : Fˣ) : F)
        = σ ((weilPairingMu h₂ hpow : Fˣ) : F) := by
    rw [restrictRootsOfUnity_coe_apply]
    simp
  simp only [hcoe, algebraMap_coe_weilPairingMu]
  rw [← galoisFunctionField_algebraMap σ ((weilPairingMu h₂ hpow : Fˣ) : F),
    algebraMap_coe_weilPairingMu h₂ hpow]
  exact hgal

open Classical in
/-- **Galois-equivariance of the Weil-pairing element at the `μ_n(F)` group level (conditional
form).**

For a base-field automorphism `σ : F ≃ₐ[S] F`, a translation point `T = (x₂, y₂)` on `W⁄F`, and the
`n`-th roots `g`, `g'` attached to `S` and `σS`, the transport hypothesis
`htr : galoisFunctionField σ g = u • g'` (`u` a unit of `F[W⁄F]`) yields, as an equation in the
group `μ_n(F) = rootsOfUnity n F`,

```
restrictRootsOfUnity σ n (weilPairingMu h₂ hpow) = weilPairingMu (equation_algEquiv σ h₂) hpow',
```

i.e. `σ · e_n(S, T) = e_n(σS, σT)`.  The `μ_n(F)` group-level form of
`weilPairingElt_galois_of_transport` (#456): the equation is pushed, through the injective composite
`ζ ↦ algebraMap F F(W⁄F) ((ζ : Fˣ) : F)`, to the merged `F(W⁄F)`-level equivariance.  `n`-agnostic:
the multiplication-by-`n` structure of `g` is carried by `htr`.

⚠️ The proof is `weilPairingMu_galois_of_weilPairingElt` above applied to
`weilPairingElt_galois_of_transport`, which is all it ever was. -/
theorem weilPairingMu_galois_of_transport (σ : F ≃ₐ[S] F) (h₂ : (W⁄F).Equation x₂ y₂)
    {g g' : (W⁄F).FunctionField} {u : (W⁄F).CoordinateRingˣ} {n : ℕ} [NeZero n]
    (htr : galoisFunctionField σ g = (u : (W⁄F).CoordinateRing) • g')
    (hpow : weilPairingElt h₂ g ^ n = 1)
    (hpow' : weilPairingElt (equation_algEquiv σ h₂) g' ^ n = 1) :
    restrictRootsOfUnity (σ.toRingEquiv.toRingHom) n (weilPairingMu h₂ hpow)
      = weilPairingMu (equation_algEquiv σ h₂) hpow' :=
  weilPairingMu_galois_of_weilPairingElt σ h₂ (weilPairingElt_galois_of_transport σ h₂ htr)
    hpow hpow'

open Classical in
/-- **Galois-equivariance at the `μ_n(F)` group level (exact-transport form).**  The special case of
`weilPairingMu_galois_of_transport` where the transport is an equality on the nose,
`galoisFunctionField σ g = g'` (unit `u = 1`). -/
theorem weilPairingMu_galois_of_transport_eq (σ : F ≃ₐ[S] F) (h₂ : (W⁄F).Equation x₂ y₂)
    {g g' : (W⁄F).FunctionField} {n : ℕ} [NeZero n]
    (htr : galoisFunctionField σ g = g')
    (hpow : weilPairingElt h₂ g ^ n = 1)
    (hpow' : weilPairingElt (equation_algEquiv σ h₂) g' ^ n = 1) :
    restrictRootsOfUnity (σ.toRingEquiv.toRingHom) n (weilPairingMu h₂ hpow)
      = weilPairingMu (equation_algEquiv σ h₂) hpow' :=
  weilPairingMu_galois_of_transport σ h₂ (u := 1) (by simpa using htr) hpow hpow'

end WeierstrassCurve.Affine.CoordinateRing
