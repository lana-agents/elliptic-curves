/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.GaloisFunctionField
import EllipticCurves.FunctionField.WeilPairing

/-!
# Galois-equivariance of the Weil-pairing element `e_n(S, T)` (Weil-pairing construction, rung 6)

Let `W` be an elliptic curve over a field `S`, let `F` be a field extension of `S`, and let
`σ : F ≃ₐ[S] F` be an `S`-algebra automorphism of `F` (a Galois automorphism when `F / S` is
Galois). Working over the **base-changed curve** `W⁄F : Affine F`, the divisor-theoretic
Weil-pairing element (Silverman AEC III.8) is

```
e_n(S, T) := weilPairingElt h_T g_S = τ_T∗(g_S) / g_S ∈ F(W⁄F),
```

where `g_S` is the rung-5 `n`-th root attached to the `n`-torsion point `S` and
`τ_T∗ = translateEndo h_T` is the translation endomorphism for a second `n`-torsion point `T`.

This file establishes the **Galois-equivariance** `σ( e_n(S, T) ) = e_n(σS, σT)`, one of the three
structural properties named for the pairing in issue #419. It is delivered in the **conditional
form** sanctioned by #456: the single genuinely rung-4/5-gated input — the `g_S` transport
`σ⋆ g_S = u · g_{σS}` (equal up to a unit `u` of `F[W⁄F]`, since `g_S` is only determined up to such
a unit) — is carried as an explicit hypothesis, exactly as the sibling structural items carry
`hcomm` / `hprin` / `hsum`. Everything else — the σ-semilinear reduction, the translation-slot
equivariance, and the cancellation of the transport unit in the ratio — is unconditional and
consumes only the merged substrate:

* `galoisFunctionField σ` and its translation equivariance `galoisFunctionField_translateEndo`
  (`GaloisFunctionField.lean`, #455);
* `weilPairingElt` and `translateEndo_algebraMap_unit` (`WeilPairing.lean`, #419).

## Main statements

* `weilPairingElt_galois_of_transport` — the conditional Galois-equivariance
  `σ⋆(e_n(S, T)) = e_n(σS, σT)` from the transport hypothesis `σ⋆ g_S = u · g_{σS}`;
* `weilPairingElt_galois_of_transport_eq` — the special case of an exact transport
  `σ⋆ g_S = g_{σS}`.

The argument is **`n`-agnostic**: the multiplication-by-`n` structure of `g_S` is entirely absorbed
into the transport hypothesis, so there is no `n = 2` / `n = 3` split — the single statement covers
every `n` for which `g_S` exists. The **unconditional** form (discharging the transport hypothesis
from the rung-4/5 divisor structure `divisor g_S = [n]∗(S)` and its σ-equivariance) is deliverable 2
of #456 and waits on rung 4 (#421/#422); non-degeneracy stays out, and it is **not** Ward-gated —
`WeilPairing`'s scope section is the canonical account of what it consumes (#769).

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.
-/

namespace WeierstrassCurve.Affine.CoordinateRing

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S} [W.IsElliptic]
  {x₂ y₂ : F}

open Classical in
/-- **Galois-equivariance of the Weil-pairing element (conditional form).**

For a base-field automorphism `σ : F ≃ₐ[S] F`, a translation point `T = (x₂, y₂)` on `W⁄F`, and the
`n`-th roots `g`, `g'` attached to `S` and `σS`, the transport hypothesis

```
htr : galoisFunctionField σ g = u • g'      (u a unit of F[W⁄F], i.e. `σ⋆ g_S = u · g_{σS}`)
```

yields `σ( e_n(S, T) ) = e_n(σS, σT)`:

```
σ⋆(τ_T∗ g / g)
  = τ_{σT}∗(σ⋆ g) / σ⋆ g        [map_div₀ + galoisFunctionField_translateEndo]
  = τ_{σT}∗(u · g') / (u · g')   [htr]
  = u · τ_{σT}∗(g') / (u · g')   [τ_{σT}∗ fixes the constant unit u]
  = τ_{σT}∗(g') / g'.            [the nonzero unit u cancels in the ratio]
```

Here `σT` is the translated point `(σ x₂, σ y₂)` (`equation_algEquiv`), and the unit cancellation is
exactly the up-to-a-unit ambiguity of the rung-5 root `g_S`. The statement is `n`-agnostic: the
multiplication-by-`n` structure of `g` is fully carried by `htr`. -/
theorem weilPairingElt_galois_of_transport (σ : F ≃ₐ[S] F) (h₂ : (W⁄F).Equation x₂ y₂)
    {g g' : (W⁄F).FunctionField} {u : (W⁄F).CoordinateRingˣ}
    (htr : galoisFunctionField σ g = (u : (W⁄F).CoordinateRing) • g') :
    galoisFunctionField σ (weilPairingElt h₂ g)
      = weilPairingElt (equation_algEquiv σ h₂) g' := by
  have hA : algebraMap (W⁄F).CoordinateRing (W⁄F).FunctionField (u : (W⁄F).CoordinateRing) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (W⁄F).CoordinateRing (W⁄F).FunctionField)]
    exact u.ne_zero
  simp only [weilPairingElt]
  rw [map_div₀, galoisFunctionField_translateEndo, htr, Algebra.smul_def, map_mul,
    translateEndo_algebraMap_unit, mul_div_mul_left _ _ hA]

open Classical in
/-- **Galois-equivariance of the Weil-pairing element (exact-transport form).**  The special case of
`weilPairingElt_galois_of_transport` where the transport is an equality on the nose,
`galoisFunctionField σ g = g'` (unit `u = 1`). -/
theorem weilPairingElt_galois_of_transport_eq (σ : F ≃ₐ[S] F) (h₂ : (W⁄F).Equation x₂ y₂)
    {g g' : (W⁄F).FunctionField} (htr : galoisFunctionField σ g = g') :
    galoisFunctionField σ (weilPairingElt h₂ g)
      = weilPairingElt (equation_algEquiv σ h₂) g' :=
  weilPairingElt_galois_of_transport σ h₂ (u := 1) (by simpa using htr)

end WeierstrassCurve.Affine.CoordinateRing
