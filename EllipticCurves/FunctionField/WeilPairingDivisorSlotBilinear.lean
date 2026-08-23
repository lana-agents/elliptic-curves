/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairingProductRelationMu

/-!
# Divisor-slot bilinearity of the Weil pairing, unconditionally over `F̄` (rung 6)

For a fixed translation point `P` the Weil pairing is multiplicative in its **divisor** slot:

```
e_n(P, S) · e_n(P, T) = e_n(P, S ⊕ T).
```

`EllipticCurves.FunctionField.WeilPairingAntisymmetric` (`#723`) proves this at the `F(W)` level
and `EllipticCurves.FunctionField.WeilPairingAntisymmetricMu` (`#733`) in `μ_n(F)` — but every one
of those eight statements takes the third root `g_R` and the correction factor `w` as **data** and
assumes the product relation `hprod : g_R = g_S · g_T · w`.  Nothing in the tree instantiated any
of them.  This file does, at `n = 2` and `n = 3` over an algebraically closed field, with no
hypothesis beyond the setting.

## ⚠️ This is *cheaper* than antisymmetry, and the reason is worth stating

Antisymmetry (`WeilPairingProductRelation`, `#845`) consumes the alternating property at **three**
points, which is why it needed `#801`/`#829` first.  **Divisor-slot bilinearity consumes it
nowhere**: `weilPairingElt_divisorSlot_add_two`'s hypotheses are `hprod`, `hc`, `hf` and the
`2`-torsion of the translation point, and there is no `halt` among them.  So the assembly below is
shorter than `#845`'s and consumes a strictly smaller set of inputs; `[IsAlgClosed F]` enters only
through `exists_gS_{two,three}_of_isAlgClosed` (`#791`/`#825`), that is, only through `hprin`.

> The generalisable point: **a slot deferred in the same sentence as a harder slot inherits the
> harder slot's gate in the reader's mind.**  `hprod` was the shared word in the deferral, so
> bilinearity sat behind antisymmetry's alternating gate for several rungs without ever needing it.

## The route

Rung-5 data at `S`, `T` and `R` from `exists_gS_{two,three}_of_isAlgClosed`; `hprod` from
`exists_prod_eq_of_pullback` (`#845`), whose returned `w = c · φ k` is **already** the shape
`weilPairingElt_divisorSlot_add_{two,three}` discharge; then one application.  ⚠️ `#845`'s private
`rungFiveAlt_{two,three}` wrappers are *not* wanted here — they exist only to carry the alternating
property as well.  `R`'s torsion is derived from `hadd`, never assumed, since `W.torsion n` is an
`AddSubgroup`.

⚠️ **`P` is a fourth point, a priori independent of `S`, `T` and `R`**, and it must be `n`-torsion:
the correction factor is invisible to `e_n(P, −)` only because `τ_P` fixes `[n]∗`-pullbacks.  See
the non-vacuity section for what that costs a certificate.

## Main results

* ⚠️ the descent of the *conclusion* from `F(W)` to `μ_n(F)`,
  `weilPairingMu_divisorSlot_add_of_weilPairingElt`, is **not** here — it was written into this
  file because this is where it was first wanted, but it generalises `weilPairingMu_divisorSlot_add`
  and so duplicated that theorem's proof body across an import edge.  `#868` moved it up to
  `EllipticCurves.FunctionField.WeilPairingAntisymmetricMu`, next to the theorem it generalises.
  This file consumes it through the import;
* `exists_weilPairingElt_divisorSlot_add_two` and `_three` — bilinearity at the `F(W)` level over
  `F̄` with no hypothesis beyond the setting;
* `exists_weilPairingMu_divisorSlot_add_two` and `_three` — the same in `μ_n(F)`, with the three
  `hpow` data produced rather than assumed.

## Scope

`[Field F] [IsAlgClosed F] {W : Affine F} [W.IsElliptic]` for the four headlines; the descent
lemma they consume carries neither.

Out of scope: `hprin` over a **general** field, open at both `n`, which is what confines these to
`F̄`; general `n` (`#404`'s `ωₙ`); rung 4 (`#414`/`#421`/`#422`) — `#845` established this line
does not need it; non-degeneracy; bundling into `weilPairingMuHom` (`WeilPairingDivisorSlotHom`),
which wants a `hpow` datum uniform in the slot variable and is a different statement; any change to
`WeilPairingAntisymmetric{,Mu}`'s or `#845`'s proofs.

⚠️ **This file's headline is what the `W.Point`-level pairing's divisor slot is proved from.**  This
sentence used to read *"there is no `W.Point`-level pairing in this tree and nothing here is a step
towards one"*, and both halves are now wrong:
`EllipticCurves.FunctionField.WeilPairingFunctionTwo` (`#922`) defines
`weilPairingTwo : E[2] → E[2] → μ_2(F)`, and its `weilPairingEltTwo_add_left` — with
`weilPairingTwo_add_left` the `μ_2`-level mirror — is `exists_weilPairingElt_divisorSlot_add_two`
below, read through that file's bridge lemma.

⚠️ **The literal claim about the slot is still true, and it is why the transfer costs anything at
all**: the divisor slot here is a slot of `weilPairingElt`, which takes a *function*, not a point.
`#922` pays for the gap in four cases — `T = O`, `S₁ = O`, `S₂ = O`, and `S₁ ⊕ S₂ = O`, where
`2`-torsion forces `S₂ = S₁` and the claim collapses to `e_2(S₁, T) ^ 2 = 1` — plus the conversion
of the roots this headline *produces* into its own root predicate.  ⚠️ It does **not** supersede
anything here: a caller holding its own roots needs exactly this shape, and nothing below should be
restated in point form.

## Non-vacuity

Every headline is certified below on `#845`'s two curves.  ⚠️ **Neither certificate can take `P`
distinct from `S`, `T` and `R`, and that is a property of the curves rather than of the
statements.**  At `n = 2` on `y² = x³ − x` there are exactly three nonzero `2`-torsion points,
`(0, 0)`, `(1, 0)` and `(−1, 0)`, and `S ⊕ T = R` already uses all three; `P` is a free variable of
the headline, so it is taken to be `S = (0, 0)` and the certificate is still a genuine
three-distinct-point instance of `S ⊕ T = R`.  At `n = 3` on `y² + y = x³` the only nameable
`3`-torsion points are `(0, 0)` and its negative `(0, −1)` — `Ψ₃ = 3X(X³ + 1)`, and the `X = −1`
fibre is `y² + y + 1 = 0`, whose roots are primitive cube roots of unity — so `P = S = T = (0, 0)`
and `R = (0, −1)` is forced.  The certificate shows the hypotheses are simultaneously satisfiable,
which is what a non-vacuity certificate is for; it does **not** exhibit `S ≠ T`.  The limitation is
inherited from `#829`/`#845`/`#855` and is stated, not repaired.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(a).
-/

namespace WeierstrassCurve.Affine

open CoordinateRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

section Two

variable [IsAlgClosed F]

open Classical in
/-- **Divisor-slot bilinearity at `n = 2`, over `F̄` with no hypothesis beyond the setting.**

```
e_2(P, g_R) = e_2(P, g_S) · e_2(P, g_T),     for  S ⊕ T = R.
```

The three roots are produced together with their rung-5 certificates, as in `#845`; unlike `#845`
the root at `R` is **exposed**, because divisor-slot bilinearity is a statement about it.

⚠️ No alternating property is consumed, at any of the four points — compare `#845`, which needs it
at three.  `[IsAlgClosed F]` enters only through `exists_gS_two_of_isAlgClosed` (`#791`).

⚠️ `R`'s `2`-torsion is **derived** from `hadd`, not assumed: `W.torsion 2` is an `AddSubgroup`.
`P`'s is assumed, and is genuinely needed — it is what makes `e_2(P, c · [2]∗k) = 1`. -/
theorem exists_weilPairingElt_divisorSlot_add_two (h2 : (2 : F) ≠ 0)
    {xP yP xS yS xT yT xR yR : F} (hP : W.Nonsingular xP yP) (hS : W.Nonsingular xS yS)
    (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmP : Point.some xP yP hP ∈ W.torsion 2) (hmS : Point.some xS yS hS ∈ W.torsion 2)
    (hmT : Point.some xT yT hT ∈ W.torsion 2)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR) :
    ∃ gS gT gR : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧ gR ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 2 = mulByTwoEndo h2 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hR.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gR ^ 2 = mulByTwoEndo h2 f) ∧
      weilPairingElt hP.left gR = weilPairingElt hP.left gS * weilPairingElt hP.left gT := by
  have hmR : Point.some xR yR hR ∈ W.torsion 2 := hadd ▸ add_mem hmS hmT
  obtain ⟨fS, hfS, hdS, gS, hgS, uS, huS⟩ := exists_gS_two_of_isAlgClosed h2 hS hmS
  obtain ⟨fT, hfT, hdT, gT, hgT, uT, huT⟩ := exists_gS_two_of_isAlgClosed h2 hT hmT
  obtain ⟨fR, hfR, hdR, gR, hgR, uR, huR⟩ := exists_gS_two_of_isAlgClosed h2 hR hmR
  obtain ⟨c, k, hc, hk, hprod⟩ :=
    exists_prod_eq_of_pullback (mulByTwoEndo h2) (mulByTwoEndo_algebraMap_base h2)
      two_ne_zero hS hT hR hadd hfS hfT hfR hdS hdT hdR hgS hgT hgR huS huT huR
  have htorsP := add_self_eq_zero_of_mem_torsion_two hmP
  exact ⟨gS, gT, gR, hgS, hgT, hgR, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩,
    ⟨fR, hfR, hdR, uR, huR⟩,
    weilPairingElt_divisorSlot_add_two hP.left h2 htorsP hc hk hprod⟩

open Classical in
/-- **Divisor-slot bilinearity at `n = 2` in `μ_n(F)`, over `F̄` with no hypothesis beyond the
setting.**

```
μ_n(P, g_R) = μ_n(P, g_S) · μ_n(P, g_T)   in rootsOfUnity n F.
```

The envelope is `exists_weilPairingElt_divisorSlot_add_two`'s, extended by the three `hpow` data:
they are bound existentially because `weilPairingMu` is indexed by the *proof*, and they are
**produced** — not assumed — from the three rung-5 certificates the envelope already carries, by
`weilPairingElt_pow_eq_one_of_gS_two_torsion` (`TranslationTorsion`) applied at `P` with each root.

⚠️ The `μ_n` index `n` is **free** here and is not tied to the `2`-torsion of the four points: the
producer's `n` is the exponent of the rung-5 relation it consumes, so it is `2` in the certificates
below, but the statement is about `weilPairingMu` at whatever `n` the caller's `hpow` data are
at. -/
theorem exists_weilPairingMu_divisorSlot_add_two (h2 : (2 : F) ≠ 0)
    {xP yP xS yS xT yT xR yR : F} (hP : W.Nonsingular xP yP) (hS : W.Nonsingular xS yS)
    (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmP : Point.some xP yP hP ∈ W.torsion 2) (hmS : Point.some xS yS hS ∈ W.torsion 2)
    (hmT : Point.some xT yT hT ∈ W.torsion 2)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR) :
    ∃ gS gT gR : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧ gR ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 2 = mulByTwoEndo h2 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hR.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gR ^ 2 = mulByTwoEndo h2 f) ∧
      ∃ hpowS : weilPairingElt hP.left gS ^ 2 = 1,
        ∃ hpowT : weilPairingElt hP.left gT ^ 2 = 1,
          ∃ hpowR : weilPairingElt hP.left gR ^ 2 = 1,
            weilPairingMu hP.left hpowR
              = weilPairingMu hP.left hpowS * weilPairingMu hP.left hpowT := by
  obtain ⟨gS, gT, gR, hgS, hgT, hgR, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩,
    ⟨fR, hfR, hdR, uR, huR⟩, hbil⟩ :=
      exists_weilPairingElt_divisorSlot_add_two h2 hP hS hT hR hmP hmS hmT hadd
  have htorsP := add_self_eq_zero_of_mem_torsion_two hmP
  have hpowS : weilPairingElt hP.left gS ^ 2 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_two_torsion hP.left h2 htorsP hgS huS
  have hpowT : weilPairingElt hP.left gT ^ 2 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_two_torsion hP.left h2 htorsP hgT huT
  have hpowR : weilPairingElt hP.left gR ^ 2 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_two_torsion hP.left h2 htorsP hgR huR
  exact ⟨gS, gT, gR, hgS, hgT, hgR, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩,
    ⟨fR, hfR, hdR, uR, huR⟩, hpowS, hpowT, hpowR,
    weilPairingMu_divisorSlot_add_of_weilPairingElt hP.left hpowS hpowT hpowR hbil⟩

end Two

section Three

variable [IsAlgClosed F]

open Classical in
/-- **Divisor-slot bilinearity at `n = 3`, over `F̄` with no hypothesis beyond the setting.**

The `n = 3` mirror of `exists_weilPairingElt_divisorSlot_add_two`; only the pullback differs,
`mulByThreeEndo h2 h3` in place of `mulByTwoEndo h2`, and with it the rung-5 producer
(`exists_gS_three_of_isAlgClosed`, `#825`) and the discharge of the correction factor
(`weilPairingElt_divisorSlot_add_three`).  No alternating property is consumed here either. -/
theorem exists_weilPairingElt_divisorSlot_add_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xP yP xS yS xT yT xR yR : F} (hP : W.Nonsingular xP yP) (hS : W.Nonsingular xS yS)
    (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmP : Point.some xP yP hP ∈ W.torsion 3) (hmS : Point.some xS yS hS ∈ W.torsion 3)
    (hmT : Point.some xT yT hT ∈ W.torsion 3)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR) :
    ∃ gS gT gR : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧ gR ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 3 = mulByThreeEndo h2 h3 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hR.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gR ^ 3 = mulByThreeEndo h2 h3 f) ∧
      weilPairingElt hP.left gR = weilPairingElt hP.left gS * weilPairingElt hP.left gT := by
  have hmR : Point.some xR yR hR ∈ W.torsion 3 := hadd ▸ add_mem hmS hmT
  obtain ⟨fS, hfS, hdS, gS, hgS, uS, huS⟩ := exists_gS_three_of_isAlgClosed h2 h3 hS hmS
  obtain ⟨fT, hfT, hdT, gT, hgT, uT, huT⟩ := exists_gS_three_of_isAlgClosed h2 h3 hT hmT
  obtain ⟨fR, hfR, hdR, gR, hgR, uR, huR⟩ := exists_gS_three_of_isAlgClosed h2 h3 hR hmR
  obtain ⟨c, k, hc, hk, hprod⟩ :=
    exists_prod_eq_of_pullback (mulByThreeEndo h2 h3) (mulByThreeEndo_algebraMap_base h2 h3)
      three_ne_zero hS hT hR hadd hfS hfT hfR hdS hdT hdR hgS hgT hgR huS huT huR
  have htorsP := add_add_self_eq_zero_of_mem_torsion_three hmP
  exact ⟨gS, gT, gR, hgS, hgT, hgR, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩,
    ⟨fR, hfR, hdR, uR, huR⟩,
    weilPairingElt_divisorSlot_add_three hP.left h2 h3 htorsP hc hk hprod⟩

open Classical in
/-- **Divisor-slot bilinearity at `n = 3` in `μ_n(F)`, over `F̄` with no hypothesis beyond the
setting.**  The `n = 3` mirror of `exists_weilPairingMu_divisorSlot_add_two`; the three `hpow` data
come from `weilPairingElt_pow_eq_one_of_gS_three_baseField` (`TranslationTriplingComm`) in place of
`weilPairingElt_pow_eq_one_of_gS_two_torsion`. -/
theorem exists_weilPairingMu_divisorSlot_add_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xP yP xS yS xT yT xR yR : F} (hP : W.Nonsingular xP yP) (hS : W.Nonsingular xS yS)
    (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmP : Point.some xP yP hP ∈ W.torsion 3) (hmS : Point.some xS yS hS ∈ W.torsion 3)
    (hmT : Point.some xT yT hT ∈ W.torsion 3)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR) :
    ∃ gS gT gR : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧ gR ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 3 = mulByThreeEndo h2 h3 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hR.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gR ^ 3 = mulByThreeEndo h2 h3 f) ∧
      ∃ hpowS : weilPairingElt hP.left gS ^ 3 = 1,
        ∃ hpowT : weilPairingElt hP.left gT ^ 3 = 1,
          ∃ hpowR : weilPairingElt hP.left gR ^ 3 = 1,
            weilPairingMu hP.left hpowR
              = weilPairingMu hP.left hpowS * weilPairingMu hP.left hpowT := by
  obtain ⟨gS, gT, gR, hgS, hgT, hgR, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩,
    ⟨fR, hfR, hdR, uR, huR⟩, hbil⟩ :=
      exists_weilPairingElt_divisorSlot_add_three h2 h3 hP hS hT hR hmP hmS hmT hadd
  have htorsP := add_add_self_eq_zero_of_mem_torsion_three hmP
  have hpowS : weilPairingElt hP.left gS ^ 3 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_three_baseField hP.left h2 h3 htorsP hgS huS
  have hpowT : weilPairingElt hP.left gT ^ 3 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_three_baseField hP.left h2 h3 htorsP hgT huT
  have hpowR : weilPairingElt hP.left gR ^ 3 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_three_baseField hP.left h2 h3 htorsP hgR huR
  exact ⟨gS, gT, gR, hgS, hgT, hgR, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩,
    ⟨fR, hfR, hdR, uR, huR⟩, hpowS, hpowT, hpowR,
    weilPairingMu_divisorSlot_add_of_weilPairingElt hP.left hpowS hpowT hpowR hbil⟩

end Three

/-! ### Non-vacuity

⚠️ See the module docstring for what the two certificates do and do not exhibit; in particular
neither can take `P` distinct from `S`, `T` and `R`, for reasons about the two curves rather than
about the statements. -/

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
/-- **Divisor-slot bilinearity at `n = 2` on a curve that exists.**  `S = (0, 0)`, `T = (1, 0)` and
`R = (−1, 0)` are the three distinct nonzero `2`-torsion points of `y² = x³ − x`, so `S ⊕ T = R` is
a genuine three-point instance.  ⚠️ The translation point is `P = S`: the curve has no fourth
`2`-torsion point to name, and `P` is a free variable of the headline. -/
example : ∃ gS gT gR : exampleCurve.FunctionField,
    weilPairingElt exampleNsS.left gR
      = weilPairingElt exampleNsS.left gS * weilPairingElt exampleNsS.left gT := by
  obtain ⟨gS, gT, gR, _, _, _, _, _, _, hbil⟩ :=
    exists_weilPairingElt_divisorSlot_add_two exampleTwo exampleNsS exampleNsS exampleNsT
      exampleNsR exampleTorS exampleTorS exampleTorT exampleAdd
  exact ⟨gS, gT, gR, hbil⟩

open Classical in
/-- **Divisor-slot bilinearity at `n = 2` in `μ_2(F)`, on a curve that exists.**  ⚠️ The three
`hpow` data are produced inside the headline from its own rung-5 certificates, so they are not an
extra burden on the caller; they are bound here because `weilPairingMu` is indexed by them. -/
example : ∃ (gS gT gR : exampleCurve.FunctionField)
    (hpowS : weilPairingElt exampleNsS.left gS ^ 2 = 1)
    (hpowT : weilPairingElt exampleNsS.left gT ^ 2 = 1)
    (hpowR : weilPairingElt exampleNsS.left gR ^ 2 = 1),
    weilPairingMu exampleNsS.left hpowR
      = weilPairingMu exampleNsS.left hpowS * weilPairingMu exampleNsS.left hpowT := by
  obtain ⟨gS, gT, gR, _, _, _, _, _, _, hpowS, hpowT, hpowR, hbil⟩ :=
    exists_weilPairingMu_divisorSlot_add_two exampleTwo exampleNsS exampleNsS exampleNsT
      exampleNsR exampleTorS exampleTorS exampleTorT exampleAdd
  exact ⟨gS, gT, gR, hpowS, hpowT, hpowR, hbil⟩

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
/-- **Divisor-slot bilinearity at `n = 3` on a curve that exists.**  ⚠️ Here `P = S = T = (0, 0)`
and `R = (0, −1)`; see the module docstring for why no other `3`-torsion point of `y² + y = x³` is
nameable. -/
example : ∃ gS gT gR : exampleCurveThree.FunctionField,
    weilPairingElt exampleNsThreeS.left gR
      = weilPairingElt exampleNsThreeS.left gS * weilPairingElt exampleNsThreeS.left gT := by
  obtain ⟨gS, gT, gR, _, _, _, _, _, _, hbil⟩ :=
    exists_weilPairingElt_divisorSlot_add_three exampleTwo exampleThree exampleNsThreeS
      exampleNsThreeS exampleNsThreeS exampleNsThreeR exampleTorThreeS exampleTorThreeS
      exampleTorThreeS exampleAddThree
  exact ⟨gS, gT, gR, hbil⟩

open Classical in
/-- **Divisor-slot bilinearity at `n = 3` in `μ_3(F)`, on a curve that exists.**  ⚠️ Here
`P = S = T = (0, 0)`; see the module docstring. -/
example : ∃ (gS gT gR : exampleCurveThree.FunctionField)
    (hpowS : weilPairingElt exampleNsThreeS.left gS ^ 3 = 1)
    (hpowT : weilPairingElt exampleNsThreeS.left gT ^ 3 = 1)
    (hpowR : weilPairingElt exampleNsThreeS.left gR ^ 3 = 1),
    weilPairingMu exampleNsThreeS.left hpowR
      = weilPairingMu exampleNsThreeS.left hpowS * weilPairingMu exampleNsThreeS.left hpowT := by
  obtain ⟨gS, gT, gR, _, _, _, _, _, _, hpowS, hpowT, hpowR, hbil⟩ :=
    exists_weilPairingMu_divisorSlot_add_three exampleTwo exampleThree exampleNsThreeS
      exampleNsThreeS exampleNsThreeS exampleNsThreeR exampleTorThreeS exampleTorThreeS
      exampleTorThreeS exampleAddThree
  exact ⟨gS, gT, gR, hpowS, hpowT, hpowR, hbil⟩

end Nonvacuity

end WeierstrassCurve.Affine
