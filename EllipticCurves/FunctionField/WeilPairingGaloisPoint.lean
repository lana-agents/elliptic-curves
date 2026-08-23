/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.GaloisClosedPoint
import EllipticCurves.FunctionField.WeilPairingGaloisDivisor

/-!
# Galois-equivariance of the Weil-pairing element from point data

`EllipticCurves.FunctionField.WeilPairingGaloisDivisor` proves the Galois-equivariance of the
Weil-pairing element from the divisor hypothesis

`hdiv : divisor (W⁄F) g' = (divisor (W⁄F) g).equivMapDomain (mapEquiv (galoisCoordRing σ))`,

and `EllipticCurves.FunctionField.GaloisClosedPoint` identifies that push-forward on the closed
points of affine points: it sends the closed point of `(x, y)` to the closed point of `(σ x, σ y)`.
Putting the two together, this file states the equivariance with `hdiv` replaced by *point* data:

`divisor g = n·(S)`   and   `divisor g' = n·(σS)`.

That is the form in which the divisor-slot input actually arrives — the rung-5 root `g_S` is
characterised by its divisor at points, not by an abstract push-forward — and it makes visible that
`g'` need only be *some* function with the transported divisor, not `σ⋆ g`: an intrinsically
constructed `g_{σS}` qualifies, and the constant ambiguity between the two is exactly what the
pairing quotient cancels.

Both levels are given, as in `WeilPairingGaloisDivisor`: the `F(W⁄F)` level and the `μ_n(F)` level,
so that a consumer working in the value group of the pairing does not have to descend to the
function field to use point data.

## Scope

Unchanged from `WeilPairingGaloisDivisor`: this is the **Galois** slot only. The hypotheses below
are discharged — rather than assumed — in `EllipticCurves.FunctionField.WeilPairingGaloisRoot`,
which is `#456` deliverable 2 and does not need `divisor g_S = [n]∗(S)`. The translation slot
(`#465` deliverable 2, the alternating property) is untouched, and non-degeneracy is out — and
**not** Ward-gated; `WeilPairing`'s scope section is the canonical account of what it
consumes (`#769`).

## Main statements

* `WeierstrassCurve.Affine.CoordinateRing.weilPairingElt_galois_of_divisor_eq_single`
* `WeierstrassCurve.Affine.CoordinateRing.weilPairingMu_galois_of_divisor_eq_single`

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine.CoordinateRing

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S} [W.IsElliptic]
  {x₂ y₂ : F}

/-- **Galois-equivariance of the Weil-pairing element, from point data.**

`σ⋆(e(T, g)) = e(σT, g')` whenever the divisor-slot function `g` has divisor `m·(S)` and `g'` has
divisor `m·(σS)`, for an affine point `S` of `W⁄F`. -/
theorem weilPairingElt_galois_of_divisor_eq_single (σ : F ≃ₐ[S] F) (h₂ : (W⁄F).Equation x₂ y₂)
    {x₃ y₃ : F} (h₃ : (W⁄F).Equation x₃ y₃) {g g' : (W⁄F).FunctionField} {m : ℤ}
    (hg : g ≠ 0) (hg' : g' ≠ 0)
    (hgdiv : divisor (W⁄F) g = Finsupp.single (pointClosedPoint h₃) m)
    (hg'div : divisor (W⁄F) g' = Finsupp.single (pointClosedPoint (equation_algEquiv σ h₃)) m) :
    galoisFunctionField σ (weilPairingElt h₂ g)
      = weilPairingElt (equation_algEquiv σ h₂) g' :=
  weilPairingElt_galois_of_divisor_eq σ h₂ hg hg'
    (divisor_eq_equivMapDomain_of_eq_single σ h₃ hgdiv hg'div)

open Classical in
/-- **Galois-equivariance of the Weil pairing in `μ_n(F)`, from point data.** The statement of
`weilPairingElt_galois_of_divisor_eq_single` in the value group of the pairing. -/
theorem weilPairingMu_galois_of_divisor_eq_single (σ : F ≃ₐ[S] F) (h₂ : (W⁄F).Equation x₂ y₂)
    {x₃ y₃ : F} (h₃ : (W⁄F).Equation x₃ y₃) {g g' : (W⁄F).FunctionField} {m : ℤ} {n : ℕ}
    [NeZero n] (hg : g ≠ 0) (hg' : g' ≠ 0)
    (hgdiv : divisor (W⁄F) g = Finsupp.single (pointClosedPoint h₃) m)
    (hg'div : divisor (W⁄F) g' = Finsupp.single (pointClosedPoint (equation_algEquiv σ h₃)) m)
    (hpow : weilPairingElt h₂ g ^ n = 1)
    (hpow' : weilPairingElt (equation_algEquiv σ h₂) g' ^ n = 1) :
    restrictRootsOfUnity (σ.toRingEquiv.toRingHom) n (weilPairingMu h₂ hpow)
      = weilPairingMu (equation_algEquiv σ h₂) hpow' :=
  weilPairingMu_galois_of_divisor_eq σ h₂ hg hg'
    (divisor_eq_equivMapDomain_of_eq_single σ h₃ hgdiv hg'div) hpow hpow'

end WeierstrassCurve.Affine.CoordinateRing
