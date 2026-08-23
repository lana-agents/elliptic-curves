/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.DivisorConstant
import EllipticCurves.FunctionField.DivisorTransport
import EllipticCurves.FunctionField.WeilPairingGaloisMu

/-!
# The Galois transport hypothesis of `e_n(σS, σT) = σ(e_n(S, T))`, discharged from divisor data

`EllipticCurves.FunctionField.WeilPairingGalois` (`#456`) proves the Galois-equivariance of the
divisor-theoretic Weil-pairing element in a **conditional** form: from

```
htr : galoisFunctionField σ g = u • g'          (`u` a unit of `F[W⁄F]`)
```

it derives `σ⋆(e_n(S, T)) = e_n(σS, σT)`, at the level of `F(W⁄F)`
(`weilPairingElt_galois_of_transport`) and, in
`EllipticCurves.FunctionField.WeilPairingGaloisMu`, at the level of the value group `μ_n(F)`
(`weilPairingMu_galois_of_transport`). The hypothesis `htr` is the transport of the rung-5 `n`-th
root `g_S` along `σ`, and both of those files describe it as available only once rung 4/5 lands.

**That is now only half true, and this file supplies the other half.** `htr` follows from divisor
data alone:

* `divisor_galoisFunctionField` (`EllipticCurves.FunctionField.DivisorTransport`, `#630`) —
  `div (σ⋆ f) = σ_*(div f)`, where `σ_* = Finsupp.equivMapDomain (mapEquiv (galoisCoordRing σ))` is
  the induced permutation of affine closed points;
* `Elliptic.exists_unit_of_divisor_eq` (`#402`) and its `F*`-strengthening
  `Elliptic.exists_scalar_of_divisor_eq` (`EllipticCurves.FunctionField.DivisorConstant`, `#629`) —
  equal divisors force equality up to a unit of `F[W⁄F]`, equivalently up to a scalar in `F*`.

Given a `g'` whose divisor is the `σ`-transport of the divisor of `g`, the first says `σ⋆ g` and
`g'` have the *same* divisor, and the second turns that into `htr`. So the whole Galois slot of the
pairing's structure theory is reduced to a statement about divisors, with no residual hypothesis
about function fields.

## What this changes about the gate on `#456` deliverable 2

Before: the remaining input was the `g_S` transport itself — a hypothesis with no route attached.
After: it is a statement about divisors, and no longer mentions the pairing.

That reformulation is what this file is for, and it is what made the discharge findable.
⚠️ It was accompanied here by a guess at *which* divisor statement would supply it — the rung-5
identity `divisor g_S = [n]∗(S)` together with `[n]∗(σS) = σ_*([n]∗ S)`, both rung-4-gated. That
guess was wrong, and `#456` deliverable 2 does **not** wait on rung 4:
`EllipticCurves.FunctionField.WeilPairingGaloisRoot` discharges the divisor hypothesis below from
the rung-5 *relation* rather than from the rung-5 divisor, and never computes `divisor g_S`.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.exists_unit_galoisFunctionField_of_divisor_eq` — the
  transport hypothesis `htr`, obtained from the divisor hypothesis.
* `WeierstrassCurve.Affine.CoordinateRing.exists_scalar_galoisFunctionField_of_divisor_eq` — its
  `F*`-form.
* `WeierstrassCurve.Affine.CoordinateRing.weilPairingElt_galois_of_divisor_eq` and
  `weilPairingMu_galois_of_divisor_eq` — the Galois-equivariance of `e_n`, at the level of
  `F(W⁄F)` and of `μ_n(F)`, with the divisor hypothesis in place of `htr`.

Nothing here edits `WeilPairingGalois.lean` or `WeilPairingGaloisMu.lean`; the qualification of
their "rung-4/5-gated" remarks is stated from this file, naming them.

## The translation slot has *not* moved

`translateEndo h_T` is a ring endomorphism of `F(W)` that does **not** preserve the affine
coordinate ring `F[W]` — translation moves the point(s) at infinity — so it is not
`IsFractionRing.ringEquivOfRingEquiv e` for any `e : F[W] ≃+* F[W]`, and `#630`'s transport does
not apply to it. The Galois slot is transportable and the *affine* translation slot is not; that
asymmetry is the content of `#630`'s scope note and it survives this file.
⚠️ Two things this bullet used to assert are no longer true, and neither is repaired by anything
here. The divisor-pullback-under-translation formula exists on the **projective** divisor group,
as `divisorProj_translateEndo` (`EllipticCurves.FunctionField.PlaceOrder`) — what `#630` fails to
give is the *affine* `divisor W`, which really does not transport. And that formula is not the
crux of `#465` deliverable 2: the alternating property is proved at `n = 2` and at `n = 3` over
`F̄` (`WeilPairingAlternatingTwoAlgClosed`, `WeilPairingAlternatingThreeAlgClosed`) by the
concrete telescoping route, which never pulls a divisor back along a translation.

## Non-degeneracy

Every result below is conditional on the divisor hypothesis, which any `g` with `divisor g = 0`
satisfies vacuously — and such a `g` is a constant (`#629`), for which the pairing statement says
nothing. `divisor_equivMapDomain_galoisCoordRing_genX` is the witness that this is not the only
case: the generic `x`-coordinate satisfies the hypothesis against itself, for **every** `σ`, and
`Elliptic.divisor_genX_ne_zero` (`#629`) says its divisor is nonzero. So the hypothesis is
satisfiable at a genuinely non-constant function.

## Scope

Rung-4/5-independent and Ward-independent; unconditional in `[W.IsElliptic]` (the Dedekind
hypothesis of the divisor layer is discharged by the normality instance, through the `Elliptic`
namespace of `#629`, of which this file is the first consumer). Non-degeneracy of the pairing stays
out, and it is **not** Ward-gated — `WeilPairing`'s scope section is the canonical account of what
it consumes (`#769`).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine.CoordinateRing

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S} [W.IsElliptic]
  {x₂ y₂ : F}

/-! ### The transport hypothesis, from divisor data -/

/-- **The Galois transport of a rational function is determined by its divisor.**

If `g'` has the `σ`-transported divisor of `g` — that is,
`divisor g' = σ_*(divisor g)` for the permutation `σ_* = Finsupp.equivMapDomain (mapEquiv
(galoisCoordRing σ))` of affine closed points — then `σ⋆ g` and `g'` differ by a unit of the
coordinate ring. This is exactly the hypothesis `htr` of `weilPairingElt_galois_of_transport`
(`#456`), so that theorem's transport input is a *consequence* of divisor data rather than an
extra assumption.

The proof is `divisor_galoisFunctionField` (`#630`) followed by `exists_unit_of_divisor_eq`
(`#402`). Note the unit comes out inverted: `exists_unit_of_divisor_eq` produces `u • σ⋆ g = g'`,
and `htr` wants `σ⋆ g = _ • g'`. -/
theorem exists_unit_galoisFunctionField_of_divisor_eq (σ : F ≃ₐ[S] F)
    {g g' : (W⁄F).FunctionField} (hg : g ≠ 0) (hg' : g' ≠ 0)
    (hdiv : divisor (W⁄F) g'
      = (divisor (W⁄F) g).equivMapDomain (mapEquiv (galoisCoordRing σ))) :
    ∃ u : (W⁄F).CoordinateRingˣ,
      galoisFunctionField σ g = (u : (W⁄F).CoordinateRing) • g' := by
  have hσg : galoisFunctionField σ g ≠ 0 := by
    simpa using (map_ne_zero_iff _ (galoisFunctionField σ).injective).mpr hg
  have h : divisor (W⁄F) (galoisFunctionField σ g) = divisor (W⁄F) g' := by
    rw [divisor_galoisFunctionField, hdiv]
  obtain ⟨u, hu⟩ := Elliptic.exists_unit_of_divisor_eq hσg hg' h
  exact ⟨u⁻¹, by rw [← hu, smul_smul, Units.inv_mul, one_smul]⟩

/-- **The `F*`-form of the Galois transport.** The sharp version of
`exists_unit_galoisFunctionField_of_divisor_eq`: the ambiguity is a nonzero scalar of the base
field, not merely a unit of `F[W⁄F]`.

The two are the same statement, because the units of a Weierstrass coordinate ring are exactly the
nonzero constants (`#398`, via `#629`'s `Elliptic.exists_scalar_of_divisor_eq`). The `F*` form is
the one to reach for when the transported root must be *identified* rather than merely cancelled in
a ratio: an `F[W⁄F]ˣ` is opaque, whereas an `F`-scalar is fixed by `translateEndo` and can be
compared with an `n`-th root of unity. -/
theorem exists_scalar_galoisFunctionField_of_divisor_eq (σ : F ≃ₐ[S] F)
    {g g' : (W⁄F).FunctionField} (hg : g ≠ 0) (hg' : g' ≠ 0)
    (hdiv : divisor (W⁄F) g'
      = (divisor (W⁄F) g).equivMapDomain (mapEquiv (galoisCoordRing σ))) :
    ∃ c : F, c ≠ 0 ∧
      galoisFunctionField σ g = algebraMap F (W⁄F).FunctionField c * g' := by
  have hσg : galoisFunctionField σ g ≠ 0 := by
    simpa using (map_ne_zero_iff _ (galoisFunctionField σ).injective).mpr hg
  have h : divisor (W⁄F) (galoisFunctionField σ g) = divisor (W⁄F) g' := by
    rw [divisor_galoisFunctionField, hdiv]
  obtain ⟨c, hc, hcg⟩ := Elliptic.exists_scalar_of_divisor_eq hσg hg' h
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  rw [map_inv₀, ← hcg, ← mul_assoc, inv_mul_cancel₀
    ((map_ne_zero_iff _ (algebraMap F (W⁄F).FunctionField).injective).mpr hc), one_mul]

/-! ### Galois-equivariance of `e_n` under a divisor hypothesis -/

open Classical in
/-- **Galois-equivariance of the Weil-pairing element, from divisor data.**

`σ⋆(e_n(S, T)) = e_n(σS, σT)` in `F(W⁄F)`, with the transport hypothesis of
`weilPairingElt_galois_of_transport` (`#456`) replaced by the divisor hypothesis
`divisor g' = σ_*(divisor g)`.

The hypothesis is discharged, from rung-5 data at `S` and at `σS`, in
`EllipticCurves.FunctionField.WeilPairingGaloisRoot`; over an algebraically closed base field at
`n = 2` nothing has to be supplied at all. The statement is `n`-agnostic — the
multiplication-by-`n` structure of `g` sits entirely in the divisor hypothesis. -/
theorem weilPairingElt_galois_of_divisor_eq (σ : F ≃ₐ[S] F) (h₂ : (W⁄F).Equation x₂ y₂)
    {g g' : (W⁄F).FunctionField} (hg : g ≠ 0) (hg' : g' ≠ 0)
    (hdiv : divisor (W⁄F) g'
      = (divisor (W⁄F) g).equivMapDomain (mapEquiv (galoisCoordRing σ))) :
    galoisFunctionField σ (weilPairingElt h₂ g)
      = weilPairingElt (equation_algEquiv σ h₂) g' := by
  obtain ⟨u, hu⟩ := exists_unit_galoisFunctionField_of_divisor_eq σ hg hg' hdiv
  exact weilPairingElt_galois_of_transport σ h₂ hu

open Classical in
/-- **Galois-equivariance of the Weil pairing in `μ_n(F)`, from divisor data.**

The same statement as `weilPairingElt_galois_of_divisor_eq` in the honest value group of the
pairing: `σ · e_n(S, T) = e_n(σS, σT)` as an equation in `μ_n(F) = rootsOfUnity n F`. Given at this
level as well as in `F(W⁄F)` because `EllipticCurves.FunctionField.WeilPairingGaloisMu` carries the
transport hypothesis all the way up, and a consumer working in `μ_n(F)` should not have to descend
to the function field to use a divisor hypothesis. -/
theorem weilPairingMu_galois_of_divisor_eq (σ : F ≃ₐ[S] F) (h₂ : (W⁄F).Equation x₂ y₂)
    {g g' : (W⁄F).FunctionField} {n : ℕ} [NeZero n] (hg : g ≠ 0) (hg' : g' ≠ 0)
    (hdiv : divisor (W⁄F) g'
      = (divisor (W⁄F) g).equivMapDomain (mapEquiv (galoisCoordRing σ)))
    (hpow : weilPairingElt h₂ g ^ n = 1)
    (hpow' : weilPairingElt (equation_algEquiv σ h₂) g' ^ n = 1) :
    restrictRootsOfUnity (σ.toRingEquiv.toRingHom) n (weilPairingMu h₂ hpow)
      = weilPairingMu (equation_algEquiv σ h₂) hpow' := by
  obtain ⟨u, hu⟩ := exists_unit_galoisFunctionField_of_divisor_eq σ hg hg' hdiv
  exact weilPairingMu_galois_of_transport σ h₂ hu hpow hpow'

/-! ### Non-degeneracy: the divisor hypothesis has non-constant witnesses -/

/-- **The generic `x`-coordinate satisfies the divisor hypothesis against itself**, for every `σ`.

`galoisFunctionField σ` fixes `genX` (`#455`), so `σ_*(divisor (genX)) = divisor (genX)` by
`divisor_galoisFunctionField` (`#630`). Since `Elliptic.divisor_genX_ne_zero` (`#629`) says that
divisor is **nonzero**, the hypothesis of the theorems above is satisfiable at a function that is
not a constant — the case in which they would say nothing. -/
theorem divisor_equivMapDomain_galoisCoordRing_genX (σ : F ≃ₐ[S] F) :
    divisor (W⁄F) (genX (W⁄F))
      = (divisor (W⁄F) (genX (W⁄F))).equivMapDomain (mapEquiv (galoisCoordRing σ)) := by
  rw [← divisor_galoisFunctionField, galoisFunctionField_genX]

end WeierstrassCurve.Affine.CoordinateRing
