/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.CoordinateRingNormalAlgClosed
import EllipticCurves.FunctionField.CountValuationBridge
import EllipticCurves.FunctionField.GaloisFunctionField
import EllipticCurves.FunctionField.HeightOneSpectrumMap

/-!
# Transport of orders of vanishing and divisors along a ring isomorphism

`EllipticCurves.FunctionField.HeightOneSpectrumMap` transports a closed point and its
`intValuation` along an isomorphism `e : R ≃+* S` of Dedekind domains. That transport lives on the
*ring*; the divisor calculus of `EllipticCurves.FunctionField.Divisors` lives on the *fraction
field*, through `FractionalIdeal.count`. This file crosses the gap, and then spends the result on
the Galois action.

The two halves are:

* **General Dedekind-domain algebra** (`valuation_mapEquiv`, `count_mapEquiv`) — no curve is
  mentioned, and these are upstreamable to Mathlib alongside `HeightOneSpectrum.mapEquiv` itself.
  The induced map of fraction fields is Mathlib's `IsFractionRing.ringEquivOfRingEquiv e`.
* **The Galois-equivariance of `divisor`** (`divisor_galoisFunctionField`) — for `σ : F ≃ₐ[S] F`,

  `div (σ⋆ f) = σ (div f)`,

  where `σ` acts on closed points by `HeightOneSpectrum.mapEquiv (galoisCoordRing σ)`. This is the
  divisor-level companion of the function-field-level equivariance built in
  `EllipticCurves.FunctionField.GaloisFunctionField`.

The bridge between the two encodings of the `v`-adic order — `FractionalIdeal.count` on one side,
Mathlib's `ℤᵐ⁰`-valued adic valuation on the other — is
`EllipticCurves.FunctionField.CountValuationBridge` (`#414` rung 4, Brick B). It was built for the
ramification transport of the `[n]∗` extension; this file is its second consumer, and the reason it
is worth having as a standalone brick.

## Why the Galois action is in scope and translation is not

`galoisFunctionField σ` is *by definition* the map
`IsFractionRing.ringEquivOfRingEquiv (galoisCoordRing σ)`, and `galoisCoordRing σ` is a genuine
ring **automorphism of the coordinate ring** `F[W⁄F]`: the base-changed curve is `σ`-stable, so
`σ` permutes the affine closed points. The transport therefore
applies off the shelf and the Galois results below are one-liners.

**`translateEndo h_T` is not of this form, and nothing here applies to it.** Translation by a point
is a ring endomorphism of the function field `F(W)` that does *not* preserve the affine coordinate
ring `F[W]` — it moves the point(s) at infinity — so it is not `ringEquivOfRingEquiv e` for any
`e : F[W] ≃+* F[W]`, the induced map on affine closed points is only partially defined, and the
behaviour at the excluded points is genuine mathematics rather than bookkeeping. The
divisor-pullback-under-translation formula
`divisor W (translateEndo h_T g) = (shift of divisor g)` — the crux of the product-over-`⟨T⟩`
argument for the alternating property of the Weil pairing (`#465` deliverable 2) — is therefore
**not** delivered here and is exactly as open as it was before. The same caveat is recorded in
`#526`.

## Main statements

* `IsDedekindDomain.HeightOneSpectrum.valuation_mapEquiv`
* `IsDedekindDomain.HeightOneSpectrum.count_mapEquiv`
* `WeierstrassCurve.Affine.ord_ringEquivOfRingEquiv`,
  `WeierstrassCurve.Affine.divisor_ringEquivOfRingEquiv`
* `WeierstrassCurve.Affine.CoordinateRing.ord_galoisFunctionField`,
  `WeierstrassCurve.Affine.CoordinateRing.divisor_galoisFunctionField`

## Scope

The Dedekind hypothesis `[IsDedekindDomain W.CoordinateRing]` is carried as a hypothesis, as
everywhere in the divisor layer. It is satisfiable and not a disguised falsehood, and **two
different discharges apply, at two different strengths**:

* for an **elliptic** curve over an **arbitrary** field it is a *global instance*,
  `instIsDedekindDomain` of `EllipticCurves.FunctionField.CoordinateRingNormalGeneral` — no
  `[IsAlgClosed F]`, nothing to supply by hand;
* over an **algebraically closed** field, with no `[W.IsElliptic]`, it is
  `WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain_of_isAlgClosed`.

⚠️ **This section used to name only the second**, which made it *true but weaker than the tree*,
and a reader took away "you need `F̄`". It is the second discharge that the
`### The Dedekind hypothesis is satisfiable` section exercises as an `example`, and that is not an
oversight: this file's `variable` line is `{W : Affine F}` with **no `[W.IsElliptic]`**, so the
general instance does not apply to its own subject, and `CoordinateRingNormalGeneral` is not among
its imports. Adding a `[W.IsElliptic]` sibling
`example` would therefore be a new dependency rather than a new certificate, so it is deliberately
**not** added; the general discharge is recorded here in prose, with its module named, and is
exercised where it is in scope.

⚠️ **Do not restate the algebraically-closed sentence in a file that carries `[W.IsElliptic]`** —
`EllipticCurves.FunctionField.NegYInvolution` did, and a clause that was true here became false
there.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.3 (divisors) and III.8
  (the Weil pairing).
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal

open scoped nonZeroDivisors

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain R] [IsDedekindDomain S]
  {K L : Type*} [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L]
  [IsFractionRing S L]

/-- **The adic valuation is preserved by transport along a ring isomorphism**, on the fraction
field. This is the fraction-field counterpart of `intValuation_mapEquiv`, which says the same thing
for elements of `R` itself.

The proof writes `x = r / s` with `r s : R` and reduces to the integral statement on numerator and
denominator; `IsFractionRing.ringEquivOfRingEquiv e` is precisely the isomorphism `K ≃+* L` that
agrees with `e` on the image of `R`. -/
theorem valuation_mapEquiv (e : R ≃+* S) (v : HeightOneSpectrum R) (x : K) :
    (mapEquiv e v).valuation L (IsFractionRing.ringEquivOfRingEquiv (K := K) (L := L) e x)
      = v.valuation K x := by
  obtain ⟨r, s, -, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  rw [map_div₀, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap, map_div₀, map_div₀, valuation_of_algebraMap,
    valuation_of_algebraMap, valuation_of_algebraMap, valuation_of_algebraMap,
    intValuation_mapEquiv, intValuation_mapEquiv]

/-- **The exponent of a closed point in a principal fractional ideal is preserved by transport
along a ring isomorphism.** This is `valuation_mapEquiv` in the `FractionalIdeal.count` encoding
that the divisor calculus uses, obtained through the `count ↔ valuation` bridge
`count_eq_neg_log_valuation`. -/
theorem count_mapEquiv (e : R ≃+* S) (v : HeightOneSpectrum R) (x : K) :
    count L (mapEquiv e v)
        (spanSingleton S⁰ (IsFractionRing.ringEquivOfRingEquiv (K := K) (L := L) e x))
      = count K v (spanSingleton R⁰ x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [map_zero, spanSingleton_zero, count_zero]
  · rw [count_eq_neg_log_valuation _ (by simpa using hx), count_eq_neg_log_valuation _ hx,
      valuation_mapEquiv]

end IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]

/-- **Orders of vanishing transport along a ring automorphism of the coordinate ring.** An
automorphism `e` of `F[W]` permutes the closed points by `HeightOneSpectrum.mapEquiv e` and induces
an automorphism of `F(W)`; the order of vanishing of the image at the image point is the order of
vanishing of the original at the original point. -/
theorem ord_ringEquivOfRingEquiv (e : W.CoordinateRing ≃+* W.CoordinateRing)
    (v : HeightOneSpectrum W.CoordinateRing) (f : W.FunctionField) :
    ord (mapEquiv e v)
      (IsFractionRing.ringEquivOfRingEquiv (K := W.FunctionField) (L := W.FunctionField) e f)
      = ord v f :=
  count_mapEquiv e v f

/-- **Divisors transport along a ring automorphism of the coordinate ring**: the divisor of the
image function is the divisor of the function, pushed forward along the induced permutation
`HeightOneSpectrum.mapEquiv e` of closed points. -/
theorem divisor_ringEquivOfRingEquiv (e : W.CoordinateRing ≃+* W.CoordinateRing)
    (f : W.FunctionField) :
    divisor W
        (IsFractionRing.ringEquivOfRingEquiv (K := W.FunctionField) (L := W.FunctionField) e f)
      = (divisor W f).equivMapDomain (mapEquiv e) := by
  ext w
  rw [Finsupp.equivMapDomain_apply, divisor_apply, divisor_apply,
    ← ord_ringEquivOfRingEquiv e ((mapEquiv e).symm w) f, Equiv.apply_symm_apply]

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine.CoordinateRing

open WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S}
  [IsDedekindDomain (W⁄F).CoordinateRing]

/-- **Galois-equivariance of the order of vanishing.** For `σ : F ≃ₐ[S] F`, the σ-semilinear
automorphism `σ⋆ = galoisFunctionField σ` of `F(W⁄F)` moves the closed point `v` to
`mapEquiv (galoisCoordRing σ) v`, and the order is unchanged.

This is free: `galoisFunctionField σ` is by definition the fraction-field isomorphism induced by the
coordinate-ring automorphism `galoisCoordRing σ`, so this is `ord_ringEquivOfRingEquiv`. -/
theorem ord_galoisFunctionField (σ : F ≃ₐ[S] F)
    (v : HeightOneSpectrum (W⁄F).CoordinateRing) (f : (W⁄F).FunctionField) :
    ord (mapEquiv (galoisCoordRing σ) v) (galoisFunctionField σ f) = ord v f :=
  ord_ringEquivOfRingEquiv _ v f

/-- **Galois-equivariance of the divisor**, `div (σ⋆ f) = σ (div f)`: the divisor of the
`σ`-conjugate of a rational function is the divisor of the function, pushed forward along the
permutation of closed points induced by `σ`.

This is the divisor-level companion of the function-field-level equivariance of
`EllipticCurves.FunctionField.GaloisFunctionField`, and it is what a divisor-theoretic account of
the Galois-equivariance of the Weil pairing (`#456`) works with. Note the statement is about the
*Galois* slot only; the translation slot is not touched — see the module docstring. -/
theorem divisor_galoisFunctionField (σ : F ≃ₐ[S] F) (f : (W⁄F).FunctionField) :
    divisor (W⁄F) (galoisFunctionField σ f)
      = (divisor (W⁄F) f).equivMapDomain (mapEquiv (galoisCoordRing σ)) :=
  divisor_ringEquivOfRingEquiv _ f

/-- Pointwise form of `divisor_galoisFunctionField`: the order of `σ⋆ f` at a closed point `w` is
the order of `f` at the point `w` comes from. -/
theorem ord_galoisFunctionField_apply (σ : F ≃ₐ[S] F)
    (w : HeightOneSpectrum (W⁄F).CoordinateRing) (f : (W⁄F).FunctionField) :
    ord w (galoisFunctionField σ f) = ord ((mapEquiv (galoisCoordRing σ)).symm w) f := by
  rw [← ord_galoisFunctionField σ ((mapEquiv (galoisCoordRing σ)).symm w) f,
    Equiv.apply_symm_apply]

/-- **Having trivial divisor is a Galois-stable condition.** A consequence of
`divisor_galoisFunctionField` worth naming: the property that cuts out the constants on the affine
chart is preserved and reflected by the Galois action. -/
theorem divisor_galoisFunctionField_eq_zero_iff (σ : F ≃ₐ[S] F) (f : (W⁄F).FunctionField) :
    divisor (W⁄F) (galoisFunctionField σ f) = 0 ↔ divisor (W⁄F) f = 0 := by
  constructor <;> intro h <;> ext v
  · rw [Finsupp.coe_zero, Pi.zero_apply, divisor_apply, ← ord_galoisFunctionField σ v f,
      ← divisor_apply, h, Finsupp.coe_zero, Pi.zero_apply]
  · rw [Finsupp.coe_zero, Pi.zero_apply, divisor_apply, ord_galoisFunctionField_apply,
      ← divisor_apply, h, Finsupp.coe_zero, Pi.zero_apply]

end WeierstrassCurve.Affine.CoordinateRing

/-! ### The Dedekind hypothesis is satisfiable

Every statement above carries `[IsDedekindDomain _.CoordinateRing]` as a hypothesis. Over an
algebraically closed field it is discharged, so none of the above is vacuous for want of the
hypothesis. ⚠️ That is the discharge available *here*, not the strongest one in the tree: see the
`## Scope` section of the module docstring, which records the global instance for an elliptic curve
over an arbitrary field. -/

example {F : Type*} [Field F] [IsAlgClosed F] {W : WeierstrassCurve.Affine F} [W.IsElliptic] :
    IsDedekindDomain W.CoordinateRing :=
  WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain_of_isAlgClosed
