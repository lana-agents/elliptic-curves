/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairingProductRelationMu
import EllipticCurves.FunctionField.WeilPairingRootIndependence

/-!
# Antisymmetry for roots that arrive from elsewhere, over `F̄` at both `n` (rung 6)

`EllipticCurves.FunctionField.WeilPairingProductRelation` (`#845`) proves antisymmetry

```
e_n(S, T) · e_n(T, S) = 1,     e_n(S, T) = (e_n(T, S))⁻¹
```

over an algebraically closed field with no hypothesis beyond the setting, and
`EllipticCurves.FunctionField.WeilPairingProductRelationMu` (`#855`) lifts it to the value group
`μ_n(F)`.  ⚠️ **All of those headlines *produce* their two roots existentially**: they say that
*some* pair of `n`-th roots, carrying rung-5 certificates, pairs antisymmetrically.
`weilPairingElt` takes the root as an **argument**, so a caller who already holds a root — from
`exists_gS_two_of_isAlgClosed`, say, or threaded through some other theorem — cannot apply them.

This file moves `g_S` and `g_T` from the conclusion to the hypotheses, at both `n` and at both
levels.  Nothing about curves is proved here; it is a transfer.

## The route, and it is *not* the one `#854` predicted

`#854` expected this to need the `∀ g` root-independent alternating property
(`WeilPairingRootIndependenceAlgClosed`, `#836`) and a re-run of `#845`'s assembly against a root
at `R = S ⊕ T` obtained from elsewhere — with the sourcing of that third root named as "the only
real work".

⚠️ **None of that is needed, and `#836` is not used here at all.**  The observation that collapses
it is one file older than either: `weilPairingElt_eq_of_nsmul_divisor_eq`
(`WeilPairingRootIndependence`, `#719`) says the pairing element depends on its root **only through
the root's divisor**, and the divisor is pinned by the rung-5 relation `u · g ^ n = [n]∗ f`
together with `div f`.  So two roots attached to two functions with the *same divisor* give the
*same* pairing element, and the existential headline's own roots can simply be swapped for the
caller's.

`weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq` below is that statement.  It generalises
`weilPairingElt_eq_of_smul_pow_eq` (`#719`), which needs the two roots to sit over *literally the
same* function; here they sit over two functions with the same divisor, which is what a caller
supplying their own `f_S` actually has.  ⚠️ It is generic in the pullback `φ`, for the reason `#845`
gives: nothing in the argument sees `[2]∗` or `[3]∗`, and a future divisor-level `[n]∗`
(`#403`/`#405`) instantiates it unchanged.

> **Generalisable, and it is the same shape as `#855`'s finding one rung up.**  When a theorem
> quantifies away a datum the caller wants to choose, ask whether the *conclusion* is invariant
> under changing that datum before re-running the proof that produced it.  Here the whole
> quantifier gap is closed by an invariance lemma that was already merged.

## Main results

* `weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq` — the transfer, for arbitrary `n` and arbitrary
  base-field-fixing `φ`; no `[IsAlgClosed F]`, no torsion hypothesis;
* `weilPairingElt_mul_swap_eq_one_{two,three}_of_isAlgClosed` — antisymmetry in product form for
  **given** `g_S`, `g_T`, over `F̄`, with no hypothesis beyond the setting and the caller's own
  rung-5 data;
* `weilPairingElt_eq_inv_{two,three}_of_isAlgClosed` — the quotable inverse form;
* `weilPairingMu_{mul_swap_eq_one,eq_inv}_{two,three}_of_isAlgClosed` — the same four in `μ_n(F)`.

⚠️ The register is `#829`/`#836`'s: `of_isAlgClosed` records that a *hypothesis* is discharged, not
that an instance is present.

## Scope

`[Field F] [IsAlgClosed F] {W : Affine F} [W.IsElliptic]` for the eight headlines, exactly `#845`'s
setting; the transfer lemma carries neither `[IsAlgClosed F]` nor any torsion hypothesis.  `R`'s
torsion is **derived** from `hadd` inside `#845`, never assumed here.

Out of scope: `hprin` over a **general** field, open at both `n`, which is what confines these to
`F̄`; general `n` (`#404`'s `ωₙ`); divisor-slot bilinearity, whose envelope needs `g_R` and the
correction factor as data (`#861`); non-degeneracy; any change to `#719`'s, `#723`'s, `#845`'s or
`#855`'s proofs.

⚠️ **This file does not introduce a `W.Point`-level pairing** and moving the roots into the
hypotheses is not a step towards one; `WeilPairingProductRelation`'s Scope section is right that
inventing one here would be drift.

## Non-vacuity

Every headline is certified on `#845`'s two curves, and ⚠️ **the certificates feed the theorems
roots that genuinely come from elsewhere** — `exists_gS_{two,three}_of_isAlgClosed`
(`PullbackPrincipality{Two,Three}`), not the antisymmetry headlines' own output.  That is the
property this file exists to provide, so certifying it any other way would certify the wrong thing.

⚠️ At `n = 2` the certificate is a genuine antisymmetry instance: `(0, 0)`, `(1, 0)` and `(−1, 0)`
are three **distinct** `2`-torsion points of `y² = x³ − x`, so `S ≠ T`.  At `n = 3` the only
nameable `3`-torsion points of `y² + y = x³` are `(0, 0)` and its negative `(0, −1)` — `Ψ₃ =
3X(X³ + 1)`, and the fibre over `X = −1` is `y² + y + 1 = 0`, whose roots are primitive cube roots
of unity — so the certificate is taken at `S = T = (0, 0)`, `R = (0, −1)`.  It shows the hypotheses
are simultaneously satisfiable, which is what a non-vacuity certificate is for, but it does **not**
exhibit `S ≠ T`.  That limitation is inherited from `#845`/`#855` and is not addressed here.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(d).
-/

namespace WeierstrassCurve.Affine

open CoordinateRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic] {x₂ y₂ : F}

/-! ### The transfer

One lemma, and it is the whole content of the file. -/

/-- **The Weil-pairing element depends on the rung-5 datum only through `div f`.**

If `u₁ · g₁ ^ m = φ f₁` and `u₂ · g₂ ^ m = φ f₂` with `div f₁ = div f₂`, then
`e_n(T, g₁) = e_n(T, g₂)`.

This is `weilPairingElt_eq_of_smul_pow_eq` (`WeilPairingRootIndependence`, `#719`) with "the same
function" relaxed to "the same divisor", which is the form a caller holding their own `f_S` is in.
Two functions with equal divisors differ by a unit of `F[W]` (`exists_unit_of_divisor_eq`), a unit
is a nonzero constant of `F` (`exists_eq_algebraMap_of_isUnit`, `#398`), `φ` fixes the base field by
`hφc`, and a nonzero constant has trivial divisor (`divisor_algebraMap_base`, `#629`) — so `φ f₁`
and `φ f₂` have the same divisor, and the `m`-fold divisors of the two roots agree.

⚠️ Generic in `φ`, for `#845`'s reason: nothing here sees `[2]∗` or `[3]∗`.  ⚠️ `φ` needs no
injectivity hypothesis — a ring homomorphism out of a field is injective. -/
theorem weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq (h₂ : W.Equation x₂ y₂)
    (φ : W.FunctionField →+* W.FunctionField)
    (hφc : ∀ c : F, φ (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c)
    {m : ℕ} (hm : m ≠ 0) {f₁ f₂ g₁ g₂ : W.FunctionField} (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0)
    (hfdiv : divisor W f₁ = divisor W f₂) (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    {u₁ u₂ : W.CoordinateRingˣ}
    (hu₁ : (u₁ : W.CoordinateRing) • g₁ ^ m = φ f₁)
    (hu₂ : (u₂ : W.CoordinateRing) • g₂ ^ m = φ f₂) :
    weilPairingElt h₂ g₁ = weilPairingElt h₂ g₂ := by
  obtain ⟨u, hu⟩ := exists_unit_of_divisor_eq hf₁ hf₂ hfdiv
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_isUnit u.isUnit
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact u.ne_zero (by rw [hc, map_zero])
  have hφf₁ : φ f₁ ≠ 0 := fun hz => hf₁ (φ.injective (by rw [hz, map_zero]))
  have hφeq : φ f₂ = algebraMap F W.FunctionField c * φ f₁ := by
    rw [← hu, Algebra.smul_def, hc, ← IsScalarTower.algebraMap_apply, map_mul, hφc]
  have e₁ : divisor W (g₁ ^ m) = divisor W (φ f₁) := by rw [← hu₁, divisor_units_smul]
  have e₂ : divisor W (g₂ ^ m) = divisor W (φ f₂) := by rw [← hu₂, divisor_units_smul]
  have e₃ : divisor W (φ f₂) = divisor W (φ f₁) := by
    rw [hφeq, divisor_mul
      ((map_ne_zero_iff _ (algebraMap F W.FunctionField).injective).mpr hc0) hφf₁,
      divisor_algebraMap_base hc0, zero_add]
  exact weilPairingElt_eq_of_nsmul_divisor_eq h₂ hm hg₁ hg₂
    (by rw [← divisor_pow, ← divisor_pow, e₁, e₂, e₃])

section Two

variable [IsAlgClosed F]

open Classical in
/-- **Antisymmetry at `n = 2` for roots the caller supplies**, over an algebraically closed field
with no hypothesis beyond the setting.

```
e_2(S, g_T) · e_2(T, g_S) = 1.
```

The `∀ g` form of `exists_weilPairingElt_mul_swap_eq_one_two` (`#845`): `g_S` and `g_T` are
hypotheses, each with its own `f`, that `f`'s divisor and the rung-5 relation, rather than being
produced.

⚠️ `R = S ⊕ T` is not assumed `2`-torsion; `#845` derives it from `hadd`, since `W.torsion 2` is an
`AddSubgroup`.  The proof obtains `#845`'s own pair of roots and rewrites each into the caller's by
`weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq`; the two `f`s at each point have the same divisor
because both are pinned to `2 (S)` — respectively `2 (T)` — by hypothesis. -/
theorem weilPairingElt_mul_swap_eq_one_two_of_isAlgClosed (h2 : (2 : F) ≠ 0)
    {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 2) (hmT : Point.some xT yT hT ∈ W.torsion 2)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    {fS fT gS gT : W.FunctionField} (hfS : fS ≠ 0) (hfT : fT ≠ 0)
    (hdS : divisor W fS = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ))
    (hdT : divisor W fT = Finsupp.single (pointClosedPoint hT.left) (2 : ℤ))
    (hgS : gS ≠ 0) (hgT : gT ≠ 0)
    (huS : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 fS)
    (huT : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 2 = mulByTwoEndo h2 fT) :
    weilPairingElt hS.left gT * weilPairingElt hT.left gS = 1 := by
  obtain ⟨uS, huS⟩ := huS
  obtain ⟨uT, huT⟩ := huT
  obtain ⟨gS', gT', hgS', hgT', ⟨fS', hfS', hdS', uS', huS'⟩, ⟨fT', hfT', hdT', uT', huT'⟩,
    hswap⟩ := exists_weilPairingElt_mul_swap_eq_one_two h2 hS hT hR hmS hmT hadd
  rw [weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq hS.left (mulByTwoEndo h2)
        (mulByTwoEndo_algebraMap_base h2) two_ne_zero hfT hfT' (hdT.trans hdT'.symm) hgT hgT'
        huT huT',
      weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq hT.left (mulByTwoEndo h2)
        (mulByTwoEndo_algebraMap_base h2) two_ne_zero hfS hfS' (hdS.trans hdS'.symm) hgS hgS'
        huS huS']
  exact hswap

open Classical in
/-- **Antisymmetry at `n = 2` for supplied roots, in the quotable inverse form**
`e_2(S, g_T) = (e_2(T, g_S))⁻¹`.  One line off the product form. -/
theorem weilPairingElt_eq_inv_two_of_isAlgClosed (h2 : (2 : F) ≠ 0) {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 2) (hmT : Point.some xT yT hT ∈ W.torsion 2)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    {fS fT gS gT : W.FunctionField} (hfS : fS ≠ 0) (hfT : fT ≠ 0)
    (hdS : divisor W fS = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ))
    (hdT : divisor W fT = Finsupp.single (pointClosedPoint hT.left) (2 : ℤ))
    (hgS : gS ≠ 0) (hgT : gT ≠ 0)
    (huS : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 fS)
    (huT : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 2 = mulByTwoEndo h2 fT) :
    weilPairingElt hS.left gT = (weilPairingElt hT.left gS)⁻¹ :=
  eq_inv_of_mul_eq_one_left (weilPairingElt_mul_swap_eq_one_two_of_isAlgClosed h2 hS hT hR hmS hmT
    hadd hfS hfT hdS hdT hgS hgT huS huT)

open Classical in
/-- **Antisymmetry at `n = 2` for supplied roots, in `μ_n(F)`.**

```
μ_n(S, T) · μ_n(T, S) = 1   in rootsOfUnity n F.
```

⚠️ `n` here is the index of the value group and is **not** tied to the `2`-torsion of `S` and `T`;
the two `hpow` data are hypotheses because `weilPairingMu` is indexed by the *proof*, and a caller
holding roots from elsewhere holds them.  They are not extra assumptions in practice: at a
`2`-torsion `T` they are `weilPairingElt_pow_eq_one_of_gS_two_torsion` (`TranslationTorsion`)
applied to the caller's own certificates, exactly as `#855` produces them internally.

The descent is `weilPairingMu_mul_swap_eq_one_of_weilPairingElt` (`#855`), not
`weilPairingMu_mul_swap_eq_one`, whose carried inputs are internal to `#845`'s proofs. -/
theorem weilPairingMu_mul_swap_eq_one_two_of_isAlgClosed (h2 : (2 : F) ≠ 0)
    {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 2) (hmT : Point.some xT yT hT ∈ W.torsion 2)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    {fS fT gS gT : W.FunctionField} (hfS : fS ≠ 0) (hfT : fT ≠ 0)
    (hdS : divisor W fS = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ))
    (hdT : divisor W fT = Finsupp.single (pointClosedPoint hT.left) (2 : ℤ))
    (hgS : gS ≠ 0) (hgT : gT ≠ 0)
    (huS : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 fS)
    (huT : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 2 = mulByTwoEndo h2 fT)
    {n : ℕ} [NeZero n] (hpowST : weilPairingElt hS.left gT ^ n = 1)
    (hpowTS : weilPairingElt hT.left gS ^ n = 1) :
    weilPairingMu hS.left hpowST * weilPairingMu hT.left hpowTS = 1 :=
  weilPairingMu_mul_swap_eq_one_of_weilPairingElt hS.left hT.left hpowST hpowTS
    (weilPairingElt_mul_swap_eq_one_two_of_isAlgClosed h2 hS hT hR hmS hmT hadd hfS hfT hdS hdT
      hgS hgT huS huT)

open Classical in
/-- **Antisymmetry at `n = 2` for supplied roots, in `μ_n(F)`, in the quotable inverse form.**  The
inverse is the **group** inverse of `rootsOfUnity n F`, not a transport of the field division of
`F(W)`. -/
theorem weilPairingMu_eq_inv_two_of_isAlgClosed (h2 : (2 : F) ≠ 0) {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 2) (hmT : Point.some xT yT hT ∈ W.torsion 2)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    {fS fT gS gT : W.FunctionField} (hfS : fS ≠ 0) (hfT : fT ≠ 0)
    (hdS : divisor W fS = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ))
    (hdT : divisor W fT = Finsupp.single (pointClosedPoint hT.left) (2 : ℤ))
    (hgS : gS ≠ 0) (hgT : gT ≠ 0)
    (huS : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 fS)
    (huT : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 2 = mulByTwoEndo h2 fT)
    {n : ℕ} [NeZero n] (hpowST : weilPairingElt hS.left gT ^ n = 1)
    (hpowTS : weilPairingElt hT.left gS ^ n = 1) :
    weilPairingMu hS.left hpowST = (weilPairingMu hT.left hpowTS)⁻¹ :=
  eq_inv_of_mul_eq_one_left (weilPairingMu_mul_swap_eq_one_two_of_isAlgClosed h2 hS hT hR hmS hmT
    hadd hfS hfT hdS hdT hgS hgT huS huT hpowST hpowTS)

end Two

section Three

variable [IsAlgClosed F]

open Classical in
/-- **Antisymmetry at `n = 3` for roots the caller supplies**, over an algebraically closed field
with no hypothesis beyond the setting.

The `n = 3` mirror of `weilPairingElt_mul_swap_eq_one_two_of_isAlgClosed`; only the pullback
differs, `mulByThreeEndo h2 h3` in place of `mulByTwoEndo h2`. -/
theorem weilPairingElt_mul_swap_eq_one_three_of_isAlgClosed (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 3) (hmT : Point.some xT yT hT ∈ W.torsion 3)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    {fS fT gS gT : W.FunctionField} (hfS : fS ≠ 0) (hfT : fT ≠ 0)
    (hdS : divisor W fS = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ))
    (hdT : divisor W fT = Finsupp.single (pointClosedPoint hT.left) (3 : ℤ))
    (hgS : gS ≠ 0) (hgT : gT ≠ 0)
    (huS : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 fS)
    (huT : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 3 = mulByThreeEndo h2 h3 fT) :
    weilPairingElt hS.left gT * weilPairingElt hT.left gS = 1 := by
  obtain ⟨uS, huS⟩ := huS
  obtain ⟨uT, huT⟩ := huT
  obtain ⟨gS', gT', hgS', hgT', ⟨fS', hfS', hdS', uS', huS'⟩, ⟨fT', hfT', hdT', uT', huT'⟩,
    hswap⟩ := exists_weilPairingElt_mul_swap_eq_one_three h2 h3 hS hT hR hmS hmT hadd
  rw [weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq hS.left (mulByThreeEndo h2 h3)
        (mulByThreeEndo_algebraMap_base h2 h3) three_ne_zero hfT hfT' (hdT.trans hdT'.symm) hgT
        hgT' huT huT',
      weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq hT.left (mulByThreeEndo h2 h3)
        (mulByThreeEndo_algebraMap_base h2 h3) three_ne_zero hfS hfS' (hdS.trans hdS'.symm) hgS
        hgS' huS huS']
  exact hswap

open Classical in
/-- **Antisymmetry at `n = 3` for supplied roots, in the quotable inverse form**
`e_3(S, g_T) = (e_3(T, g_S))⁻¹`. -/
theorem weilPairingElt_eq_inv_three_of_isAlgClosed (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 3) (hmT : Point.some xT yT hT ∈ W.torsion 3)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    {fS fT gS gT : W.FunctionField} (hfS : fS ≠ 0) (hfT : fT ≠ 0)
    (hdS : divisor W fS = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ))
    (hdT : divisor W fT = Finsupp.single (pointClosedPoint hT.left) (3 : ℤ))
    (hgS : gS ≠ 0) (hgT : gT ≠ 0)
    (huS : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 fS)
    (huT : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 3 = mulByThreeEndo h2 h3 fT) :
    weilPairingElt hS.left gT = (weilPairingElt hT.left gS)⁻¹ :=
  eq_inv_of_mul_eq_one_left (weilPairingElt_mul_swap_eq_one_three_of_isAlgClosed h2 h3 hS hT hR
    hmS hmT hadd hfS hfT hdS hdT hgS hgT huS huT)

open Classical in
/-- **Antisymmetry at `n = 3` for supplied roots, in `μ_n(F)`.**  The `n = 3` mirror of
`weilPairingMu_mul_swap_eq_one_two_of_isAlgClosed`; the two `hpow` data come from
`weilPairingElt_pow_eq_one_of_gS_three_baseField` (`TranslationTriplingComm`) when the caller wants
them from their own certificates. -/
theorem weilPairingMu_mul_swap_eq_one_three_of_isAlgClosed (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 3) (hmT : Point.some xT yT hT ∈ W.torsion 3)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    {fS fT gS gT : W.FunctionField} (hfS : fS ≠ 0) (hfT : fT ≠ 0)
    (hdS : divisor W fS = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ))
    (hdT : divisor W fT = Finsupp.single (pointClosedPoint hT.left) (3 : ℤ))
    (hgS : gS ≠ 0) (hgT : gT ≠ 0)
    (huS : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 fS)
    (huT : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 3 = mulByThreeEndo h2 h3 fT)
    {n : ℕ} [NeZero n] (hpowST : weilPairingElt hS.left gT ^ n = 1)
    (hpowTS : weilPairingElt hT.left gS ^ n = 1) :
    weilPairingMu hS.left hpowST * weilPairingMu hT.left hpowTS = 1 :=
  weilPairingMu_mul_swap_eq_one_of_weilPairingElt hS.left hT.left hpowST hpowTS
    (weilPairingElt_mul_swap_eq_one_three_of_isAlgClosed h2 h3 hS hT hR hmS hmT hadd hfS hfT hdS
      hdT hgS hgT huS huT)

open Classical in
/-- **Antisymmetry at `n = 3` for supplied roots, in `μ_n(F)`, in the quotable inverse form.** -/
theorem weilPairingMu_eq_inv_three_of_isAlgClosed (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 3) (hmT : Point.some xT yT hT ∈ W.torsion 3)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    {fS fT gS gT : W.FunctionField} (hfS : fS ≠ 0) (hfT : fT ≠ 0)
    (hdS : divisor W fS = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ))
    (hdT : divisor W fT = Finsupp.single (pointClosedPoint hT.left) (3 : ℤ))
    (hgS : gS ≠ 0) (hgT : gT ≠ 0)
    (huS : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 fS)
    (huT : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 3 = mulByThreeEndo h2 h3 fT)
    {n : ℕ} [NeZero n] (hpowST : weilPairingElt hS.left gT ^ n = 1)
    (hpowTS : weilPairingElt hT.left gS ^ n = 1) :
    weilPairingMu hS.left hpowST = (weilPairingMu hT.left hpowTS)⁻¹ :=
  eq_inv_of_mul_eq_one_left (weilPairingMu_mul_swap_eq_one_three_of_isAlgClosed h2 h3 hS hT hR hmS
    hmT hadd hfS hfT hdS hdT hgS hgT huS huT hpowST hpowTS)

end Three

/-! ### Non-vacuity

⚠️ The certificates below obtain their roots from `exists_gS_{two,three}_of_isAlgClosed`, i.e. from
a route **other** than the antisymmetry headlines themselves.  That is the whole point of this
file, so certifying it with `#845`'s own output would certify the wrong thing.  See the module
docstring for what the `n = 3` certificate does and does not exhibit. -/

section Nonvacuity

/-- An algebraically closed field of characteristic zero. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

private lemma exampleTwo : (2 : exampleField) ≠ 0 := by norm_num

private lemma exampleThree : (3 : exampleField) ≠ 0 := by norm_num

/-- The curve `y² = x³ − x` over `AlgebraicClosure ℚ`, of discriminant `64`. -/
private noncomputable def exampleCurve : Affine exampleField := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleNsS : exampleCurve.Nonsingular 0 0 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

private lemma exampleNsT : exampleCurve.Nonsingular 1 0 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

private lemma exampleNsR : exampleCurve.Nonsingular (-1) 0 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

open Classical in
private lemma exampleTorS :
    Point.some (0 : exampleField) 0 exampleNsS ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNsS).mpr (by norm_num [exampleCurve])

open Classical in
private lemma exampleTorT :
    Point.some (1 : exampleField) 0 exampleNsT ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNsT).mpr (by norm_num [exampleCurve])

open Classical in
/-- `(0, 0) ⊕ (1, 0) = (−1, 0)` on `y² = x³ − x`: the three nonzero `2`-torsion points, and they
are **distinct**. -/
private lemma exampleAdd :
    Point.some (0 : exampleField) 0 exampleNsS + Point.some (1 : exampleField) 0 exampleNsT
      = Point.some (-1 : exampleField) 0 exampleNsR := by
  rw [Point.add_of_X_ne (by norm_num)]
  simp only [Point.some.injEq]
  norm_num [exampleCurve, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.negY]

open Classical in
/-- **Antisymmetry at `n = 2` on a curve that exists, for roots produced elsewhere**, at two
**distinct** named `2`-torsion points.  The two roots come from `exists_gS_two_of_isAlgClosed`,
which is exactly the situation `#845`'s existential headline cannot serve. -/
example : ∃ gS gT : exampleCurve.FunctionField,
    weilPairingElt exampleNsS.left gT * weilPairingElt exampleNsT.left gS = 1 := by
  obtain ⟨fS, hfS, hdS, gS, hgS, huS⟩ :=
    exists_gS_two_of_isAlgClosed exampleTwo exampleNsS exampleTorS
  obtain ⟨fT, hfT, hdT, gT, hgT, huT⟩ :=
    exists_gS_two_of_isAlgClosed exampleTwo exampleNsT exampleTorT
  exact ⟨gS, gT, weilPairingElt_mul_swap_eq_one_two_of_isAlgClosed exampleTwo exampleNsS
    exampleNsT exampleNsR exampleTorS exampleTorT exampleAdd hfS hfT hdS hdT hgS hgT huS huT⟩

open Classical in
/-- **The inverse form at `n = 2`, on a curve that exists**, for roots produced elsewhere. -/
example : ∃ gS gT : exampleCurve.FunctionField,
    weilPairingElt exampleNsS.left gT = (weilPairingElt exampleNsT.left gS)⁻¹ := by
  obtain ⟨fS, hfS, hdS, gS, hgS, huS⟩ :=
    exists_gS_two_of_isAlgClosed exampleTwo exampleNsS exampleTorS
  obtain ⟨fT, hfT, hdT, gT, hgT, huT⟩ :=
    exists_gS_two_of_isAlgClosed exampleTwo exampleNsT exampleTorT
  exact ⟨gS, gT, weilPairingElt_eq_inv_two_of_isAlgClosed exampleTwo exampleNsS exampleNsT
    exampleNsR exampleTorS exampleTorT exampleAdd hfS hfT hdS hdT hgS hgT huS huT⟩

open Classical in
/-- **The `μ_n(F)` product form at `n = 2`, on a curve that exists**, for roots produced elsewhere.
⚠️ The two `hpow` data are produced from the same certificates by
`weilPairingElt_pow_eq_one_of_gS_two_torsion`, which is the point of the remark in that theorem's
docstring: they are not an extra assumption on the caller. -/
example : ∃ (gS gT : exampleCurve.FunctionField)
    (hpowST : weilPairingElt exampleNsS.left gT ^ 2 = 1)
    (hpowTS : weilPairingElt exampleNsT.left gS ^ 2 = 1),
    weilPairingMu exampleNsS.left hpowST * weilPairingMu exampleNsT.left hpowTS = 1 := by
  obtain ⟨fS, hfS, hdS, gS, hgS, huS⟩ :=
    exists_gS_two_of_isAlgClosed exampleTwo exampleNsS exampleTorS
  obtain ⟨fT, hfT, hdT, gT, hgT, huT⟩ :=
    exists_gS_two_of_isAlgClosed exampleTwo exampleNsT exampleTorT
  obtain ⟨uS, huS'⟩ := huS
  obtain ⟨uT, huT'⟩ := huT
  refine ⟨gS, gT, weilPairingElt_pow_eq_one_of_gS_two_torsion exampleNsS.left exampleTwo
      (add_self_eq_zero_of_mem_torsion_two exampleTorS) hgT huT',
    weilPairingElt_pow_eq_one_of_gS_two_torsion exampleNsT.left exampleTwo
      (add_self_eq_zero_of_mem_torsion_two exampleTorT) hgS huS', ?_⟩
  exact weilPairingMu_mul_swap_eq_one_two_of_isAlgClosed exampleTwo exampleNsS exampleNsT
    exampleNsR exampleTorS exampleTorT exampleAdd hfS hfT hdS hdT hgS hgT ⟨uS, huS'⟩ ⟨uT, huT'⟩ _ _

open Classical in
/-- **The `μ_n(F)` inverse form at `n = 2`, on a curve that exists**, for roots produced
elsewhere. -/
example : ∃ (gS gT : exampleCurve.FunctionField)
    (hpowST : weilPairingElt exampleNsS.left gT ^ 2 = 1)
    (hpowTS : weilPairingElt exampleNsT.left gS ^ 2 = 1),
    weilPairingMu exampleNsS.left hpowST = (weilPairingMu exampleNsT.left hpowTS)⁻¹ := by
  obtain ⟨fS, hfS, hdS, gS, hgS, huS⟩ :=
    exists_gS_two_of_isAlgClosed exampleTwo exampleNsS exampleTorS
  obtain ⟨fT, hfT, hdT, gT, hgT, huT⟩ :=
    exists_gS_two_of_isAlgClosed exampleTwo exampleNsT exampleTorT
  obtain ⟨uS, huS'⟩ := huS
  obtain ⟨uT, huT'⟩ := huT
  refine ⟨gS, gT, weilPairingElt_pow_eq_one_of_gS_two_torsion exampleNsS.left exampleTwo
      (add_self_eq_zero_of_mem_torsion_two exampleTorS) hgT huT',
    weilPairingElt_pow_eq_one_of_gS_two_torsion exampleNsT.left exampleTwo
      (add_self_eq_zero_of_mem_torsion_two exampleTorT) hgS huS', ?_⟩
  exact weilPairingMu_eq_inv_two_of_isAlgClosed exampleTwo exampleNsS exampleNsT exampleNsR
    exampleTorS exampleTorT exampleAdd hfS hfT hdS hdT hgS hgT ⟨uS, huS'⟩ ⟨uT, huT'⟩ _ _

/-- The curve `y² + y = x³` over `AlgebraicClosure ℚ`, of discriminant `−27`. -/
private noncomputable def exampleCurveThree : Affine exampleField := ⟨0, 0, 1, 0, 0⟩

private instance : exampleCurveThree.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurveThree, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleNsThreeS : exampleCurveThree.Nonsingular 0 0 :=
  exampleCurveThree.equation_iff_nonsingular.mp (by
    norm_num [exampleCurveThree, WeierstrassCurve.Affine.equation_iff])

private lemma exampleNsThreeR : exampleCurveThree.Nonsingular 0 (-1) :=
  exampleCurveThree.equation_iff_nonsingular.mp (by
    norm_num [exampleCurveThree, WeierstrassCurve.Affine.equation_iff])

open Classical in
private lemma exampleTorThreeS :
    Point.some (0 : exampleField) 0 exampleNsThreeS ∈ exampleCurveThree.torsion 3 :=
  mem_torsion_three_some_iff'.mpr (by
    norm_num [exampleCurveThree, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈])

open Classical in
/-- `(0, 0) ⊕ (0, 0) = (0, −1)` on `y² + y = x³`: doubling the named `3`-torsion point gives its
negative, which is the other one. -/
private lemma exampleAddThree :
    Point.some (0 : exampleField) 0 exampleNsThreeS
        + Point.some (0 : exampleField) 0 exampleNsThreeS
      = Point.some (0 : exampleField) (-1) exampleNsThreeR := by
  rw [Point.add_of_Y_ne (by norm_num [exampleCurveThree, WeierstrassCurve.Affine.negY])]
  simp only [Point.some.injEq]
  norm_num [exampleCurveThree, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.negY]

open Classical in
/-- **Antisymmetry at `n = 3` on a curve that exists, for roots produced elsewhere.**  ⚠️ Here
`S = T`; see the module docstring. -/
example : ∃ gS gT : exampleCurveThree.FunctionField,
    weilPairingElt exampleNsThreeS.left gT * weilPairingElt exampleNsThreeS.left gS = 1 := by
  obtain ⟨fS, hfS, hdS, gS, hgS, huS⟩ :=
    exists_gS_three_of_isAlgClosed exampleTwo exampleThree exampleNsThreeS exampleTorThreeS
  obtain ⟨fT, hfT, hdT, gT, hgT, huT⟩ :=
    exists_gS_three_of_isAlgClosed exampleTwo exampleThree exampleNsThreeS exampleTorThreeS
  exact ⟨gS, gT, weilPairingElt_mul_swap_eq_one_three_of_isAlgClosed exampleTwo exampleThree
    exampleNsThreeS exampleNsThreeS exampleNsThreeR exampleTorThreeS exampleTorThreeS
    exampleAddThree hfS hfT hdS hdT hgS hgT huS huT⟩

open Classical in
/-- **The inverse form at `n = 3`, on a curve that exists**, for roots produced elsewhere.  ⚠️ Here
`S = T`; see the module docstring. -/
example : ∃ gS gT : exampleCurveThree.FunctionField,
    weilPairingElt exampleNsThreeS.left gT = (weilPairingElt exampleNsThreeS.left gS)⁻¹ := by
  obtain ⟨fS, hfS, hdS, gS, hgS, huS⟩ :=
    exists_gS_three_of_isAlgClosed exampleTwo exampleThree exampleNsThreeS exampleTorThreeS
  obtain ⟨fT, hfT, hdT, gT, hgT, huT⟩ :=
    exists_gS_three_of_isAlgClosed exampleTwo exampleThree exampleNsThreeS exampleTorThreeS
  exact ⟨gS, gT, weilPairingElt_eq_inv_three_of_isAlgClosed exampleTwo exampleThree
    exampleNsThreeS exampleNsThreeS exampleNsThreeR exampleTorThreeS exampleTorThreeS
    exampleAddThree hfS hfT hdS hdT hgS hgT huS huT⟩

open Classical in
/-- **The `μ_n(F)` product form at `n = 3`, on a curve that exists**, for roots produced elsewhere.
⚠️ Here `S = T`; see the module docstring. -/
example : ∃ (gS gT : exampleCurveThree.FunctionField)
    (hpowST : weilPairingElt exampleNsThreeS.left gT ^ 3 = 1)
    (hpowTS : weilPairingElt exampleNsThreeS.left gS ^ 3 = 1),
    weilPairingMu exampleNsThreeS.left hpowST * weilPairingMu exampleNsThreeS.left hpowTS = 1 := by
  obtain ⟨fS, hfS, hdS, gS, hgS, uS, huS⟩ :=
    exists_gS_three_of_isAlgClosed exampleTwo exampleThree exampleNsThreeS exampleTorThreeS
  obtain ⟨fT, hfT, hdT, gT, hgT, uT, huT⟩ :=
    exists_gS_three_of_isAlgClosed exampleTwo exampleThree exampleNsThreeS exampleTorThreeS
  have htors := add_add_self_eq_zero_of_mem_torsion_three exampleTorThreeS
  refine ⟨gS, gT, weilPairingElt_pow_eq_one_of_gS_three_baseField exampleNsThreeS.left exampleTwo
      exampleThree htors hgT huT,
    weilPairingElt_pow_eq_one_of_gS_three_baseField exampleNsThreeS.left exampleTwo exampleThree
      htors hgS huS, ?_⟩
  exact weilPairingMu_mul_swap_eq_one_three_of_isAlgClosed exampleTwo exampleThree
    exampleNsThreeS exampleNsThreeS exampleNsThreeR exampleTorThreeS exampleTorThreeS
    exampleAddThree hfS hfT hdS hdT hgS hgT ⟨uS, huS⟩ ⟨uT, huT⟩ _ _

open Classical in
/-- **The `μ_n(F)` inverse form at `n = 3`, on a curve that exists**, for roots produced elsewhere.
⚠️ Here `S = T`; see the module docstring. -/
example : ∃ (gS gT : exampleCurveThree.FunctionField)
    (hpowST : weilPairingElt exampleNsThreeS.left gT ^ 3 = 1)
    (hpowTS : weilPairingElt exampleNsThreeS.left gS ^ 3 = 1),
    weilPairingMu exampleNsThreeS.left hpowST = (weilPairingMu exampleNsThreeS.left hpowTS)⁻¹ := by
  obtain ⟨fS, hfS, hdS, gS, hgS, uS, huS⟩ :=
    exists_gS_three_of_isAlgClosed exampleTwo exampleThree exampleNsThreeS exampleTorThreeS
  obtain ⟨fT, hfT, hdT, gT, hgT, uT, huT⟩ :=
    exists_gS_three_of_isAlgClosed exampleTwo exampleThree exampleNsThreeS exampleTorThreeS
  have htors := add_add_self_eq_zero_of_mem_torsion_three exampleTorThreeS
  refine ⟨gS, gT, weilPairingElt_pow_eq_one_of_gS_three_baseField exampleNsThreeS.left exampleTwo
      exampleThree htors hgT huT,
    weilPairingElt_pow_eq_one_of_gS_three_baseField exampleNsThreeS.left exampleTwo exampleThree
      htors hgS huS, ?_⟩
  exact weilPairingMu_eq_inv_three_of_isAlgClosed exampleTwo exampleThree exampleNsThreeS
    exampleNsThreeS exampleNsThreeR exampleTorThreeS exampleTorThreeS exampleAddThree hfS hfT
    hdS hdT hgS hgT ⟨uS, huS⟩ ⟨uT, huT⟩ _ _

end Nonvacuity

end WeierstrassCurve.Affine
