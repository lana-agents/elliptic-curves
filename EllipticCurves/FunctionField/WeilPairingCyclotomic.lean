/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Galois.CyclotomicCharacter
import EllipticCurves.FunctionField.WeilPairingGaloisPoint

/-!
# `e_n(σS, σT) = e_n(S, T) ^ χ_n(σ)` — the Weil-pairing equivariance in cyclotomic form

The Galois-equivariance of the divisor-theoretic Weil pairing is merged in the form

```
restrictRootsOfUnity σ n (e_n(S, T)) = e_n(σS, σT)
```

(`weilPairingMu_galois_of_transport`, `weilPairingMu_galois_of_divisor_eq`), i.e. `σ · e_n(S, T) =
e_n(σS, σT)` as an equation in `μ_n(F)`. That is not yet the classical statement of Silverman
AEC III.8.1(d), which computes the action of `σ` explicitly:

```
e_n(σS, σT) = e_n(S, T) ^ χ_n(σ),
```

with `χ_n` the mod-`n` cyclotomic character of `F / S`. The missing step is that the Galois action
on `μ_n(F)` *is* raising to the power `χ_n(σ)`, which is
`restrictRootsOfUnity_eq_pow_galoisModularCyclotomicChar` in
`EllipticCurves.Galois.CyclotomicCharacter`. This file takes it.

The rewrite is worth having in its own right: the exponent form is the one that composes. Applied to
a basis of `E[n]` it computes `det ρ_{E,n}` as a power of `χ_n`, which is why every docstring in
`EllipticCurves.TateModule` that mentions the cyclotomic character points at the Weil pairing.

## The `ℓ`-adic level

`weilPairingMu_galois_of_transport_eq_pow_padic` is the same statement at `n = p ^ k` with the
exponent read off the `p`-adic character `χ_p` instead of `χ_{p ^ k}`, through
`galoisCyclotomicChar_toZModPow`. `T_ℓ E` is the inverse limit of the `E[ℓ ^ k]`, so this is the
level at which `det ρ_{E,ℓ} = χ_ℓ` will actually be proved, and stating it here fixes the shape.

## Three mod-`n` forms

The equivariance is merged in three shapes — from transport data, from divisor data, and from point
data (`EllipticCurves.FunctionField.WeilPairingGaloisPoint`) — and each is rewritten here, so that
a consumer holding any one of them gets the exponent form without a detour.

## Scope — hypotheses inherited verbatim

Nothing here weakens or strengthens the hypotheses of the merged equivariance statements: the
transport hypothesis `htr` (respectively the divisor hypothesis `hdiv`) is passed straight through,
and only the *conclusion* is rewritten. In particular there is no longer a residual gate to
inherit: the **unconditional** Galois-equivariance is merged in
`EllipticCurves.FunctionField.WeilPairingGaloisRoot`, which discharges `htr` and `hdiv` from
rung-5 data without ever computing `divisor g_S`, so a consumer holding it reaches the exponent
form below directly. ⚠️ At the `μ_n(F)` level that file goes one step further over an
algebraically closed base field: `exists_weilPairingMu_galois_two` / `_three` (`#859`) carry no
rung-5 data and no `hpow` proof at all, only the `n`-torsion of the two points. ⚠️ Earlier text
here named `divisor g_S = [n]∗(S)` (`#418`, gated on `#421` / `#422`) as that gate; it is not,
and the identity itself remains open and out of scope.
Non-degeneracy of the pairing stays out, and it is **not** Ward-gated — `WeilPairing`'s
scope section is the canonical account of what it consumes (`#769`). Nothing here touches the
alternating property (`#465` deliverable 2).

## Main statements

* `WeierstrassCurve.Affine.CoordinateRing.weilPairingMu_galois_of_transport_eq_pow`
* `WeierstrassCurve.Affine.CoordinateRing.weilPairingMu_galois_of_divisor_eq_pow`
* `WeierstrassCurve.Affine.CoordinateRing.weilPairingMu_galois_of_divisor_eq_single_pow`
* `WeierstrassCurve.Affine.CoordinateRing.weilPairingMu_galois_of_transport_eq_pow_padic`

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(d).
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine.CoordinateRing

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S} [W.IsElliptic]
  {x₂ y₂ : F}

/-! ### The mod-`n` statement -/

open Classical in
/-- **`e_n(σS, σT) = e_n(S, T) ^ χ_n(σ)`, from transport data** (Silverman AEC III.8.1(d)).

The merged equivariance `weilPairingMu_galois_of_transport` with its conclusion's Galois action
evaluated: by `restrictRootsOfUnity_eq_pow_galoisModularCyclotomicChar` that action is raising to
the power `χ_n(σ)`. The hypothesis `htr : σ⋆ g = u • g'` is the same one, unchanged. -/
theorem weilPairingMu_galois_of_transport_eq_pow (σ : F ≃ₐ[S] F) (h₂ : (W⁄F).Equation x₂ y₂)
    {g g' : (W⁄F).FunctionField} {u : (W⁄F).CoordinateRingˣ} {n : ℕ} [NeZero n]
    (hn : Nat.card { x // x ∈ rootsOfUnity n F } = n)
    (htr : galoisFunctionField σ g = (u : (W⁄F).CoordinateRing) • g')
    (hpow : weilPairingElt h₂ g ^ n = 1)
    (hpow' : weilPairingElt (equation_algEquiv σ h₂) g' ^ n = 1) :
    weilPairingMu (equation_algEquiv σ h₂) hpow'
      = weilPairingMu h₂ hpow ^ ((galoisModularCyclotomicChar S F hn σ : ZMod n)).val := by
  rw [← weilPairingMu_galois_of_transport σ h₂ htr hpow hpow',
    restrictRootsOfUnity_eq_pow_galoisModularCyclotomicChar]

open Classical in
/-- **`e_n(σS, σT) = e_n(S, T) ^ χ_n(σ)`, from divisor data.**

The same rewrite applied to `weilPairingMu_galois_of_divisor_eq`, whose hypothesis is that `g'` has
the `σ`-transported divisor of `g`. This is the form a rung-5 root `g_S`, characterised by its
divisor, will arrive in. -/
theorem weilPairingMu_galois_of_divisor_eq_pow (σ : F ≃ₐ[S] F) (h₂ : (W⁄F).Equation x₂ y₂)
    {g g' : (W⁄F).FunctionField} {n : ℕ} [NeZero n]
    (hn : Nat.card { x // x ∈ rootsOfUnity n F } = n) (hg : g ≠ 0) (hg' : g' ≠ 0)
    (hdiv : divisor (W⁄F) g'
      = (divisor (W⁄F) g).equivMapDomain (mapEquiv (galoisCoordRing σ)))
    (hpow : weilPairingElt h₂ g ^ n = 1)
    (hpow' : weilPairingElt (equation_algEquiv σ h₂) g' ^ n = 1) :
    weilPairingMu (equation_algEquiv σ h₂) hpow'
      = weilPairingMu h₂ hpow ^ ((galoisModularCyclotomicChar S F hn σ : ZMod n)).val := by
  rw [← weilPairingMu_galois_of_divisor_eq σ h₂ hg hg' hdiv hpow hpow',
    restrictRootsOfUnity_eq_pow_galoisModularCyclotomicChar]

open Classical in
/-- **`e_n(σS, σT) = e_n(S, T) ^ χ_n(σ)`, from point data.**

The same rewrite applied to `weilPairingMu_galois_of_divisor_eq_single` of
`EllipticCurves.FunctionField.WeilPairingGaloisPoint`, whose hypotheses are that `g` has divisor
`m·(S)` and `g'` has divisor `m·(σS)` at *affine points*. Of the three mod-`n` forms this is the
one a rung-5 root arrives in, since `g_S` is characterised by its divisor at a point rather than by
an abstract push-forward. -/
theorem weilPairingMu_galois_of_divisor_eq_single_pow (σ : F ≃ₐ[S] F)
    (h₂ : (W⁄F).Equation x₂ y₂) {x₃ y₃ : F} (h₃ : (W⁄F).Equation x₃ y₃)
    {g g' : (W⁄F).FunctionField} {m : ℤ} {n : ℕ} [NeZero n]
    (hn : Nat.card { x // x ∈ rootsOfUnity n F } = n) (hg : g ≠ 0) (hg' : g' ≠ 0)
    (hgdiv : divisor (W⁄F) g = Finsupp.single (pointClosedPoint h₃) m)
    (hg'div : divisor (W⁄F) g' = Finsupp.single (pointClosedPoint (equation_algEquiv σ h₃)) m)
    (hpow : weilPairingElt h₂ g ^ n = 1)
    (hpow' : weilPairingElt (equation_algEquiv σ h₂) g' ^ n = 1) :
    weilPairingMu (equation_algEquiv σ h₂) hpow'
      = weilPairingMu h₂ hpow ^ ((galoisModularCyclotomicChar S F hn σ : ZMod n)).val := by
  rw [← weilPairingMu_galois_of_divisor_eq_single σ h₂ h₃ hg hg' hgdiv hg'div hpow hpow',
    restrictRootsOfUnity_eq_pow_galoisModularCyclotomicChar]

/-! ### The `p`-adic level -/

open Classical in
/-- **`e_{p^k}(σS, σT) = e_{p^k}(S, T) ^ χ_p(σ)`**, with the exponent read off the `p`-adic
cyclotomic character rather than the mod-`p ^ k` one.

The exponent `((χ_p σ).val.toZModPow k).val` is the same natural number as
`(χ_{p ^ k} σ).val` (`galoisCyclotomicChar_toZModPow`), so this is
`weilPairingMu_galois_of_transport_eq_pow` at `n = p ^ k` with the levels of `χ_p` substituted. It
is the shape in which the identification `det ρ_{E,p} = χ_p` will consume the pairing, since
`T_p E` is assembled from the levels `E[p ^ k]` and a single character has to serve all of them. -/
theorem weilPairingMu_galois_of_transport_eq_pow_padic (p k : ℕ) [Fact p.Prime]
    [∀ i, HasEnoughRootsOfUnity F (p ^ i)] (σ : F ≃ₐ[S] F) (h₂ : (W⁄F).Equation x₂ y₂)
    {g g' : (W⁄F).FunctionField} {u : (W⁄F).CoordinateRingˣ}
    (htr : galoisFunctionField σ g = (u : (W⁄F).CoordinateRing) • g')
    (hpow : weilPairingElt h₂ g ^ p ^ k = 1)
    (hpow' : weilPairingElt (equation_algEquiv σ h₂) g' ^ p ^ k = 1) :
    weilPairingMu (equation_algEquiv σ h₂) hpow'
      = weilPairingMu h₂ hpow ^ ((galoisCyclotomicChar S F p σ).val.toZModPow k).val := by
  rw [galoisCyclotomicChar_toZModPow p σ k]
  exact weilPairingMu_galois_of_transport_eq_pow σ h₂
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity F (p ^ k)) htr hpow hpow'

end WeierstrassCurve.Affine.CoordinateRing
