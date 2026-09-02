/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.WeilPairingAlternatingBaseChange
import EllipticCurves.FunctionField.WeilPairingProductRelationMu

/-!
# Antisymmetry of the Weil pairing over an ARBITRARY field, with `hprin` the only gate (rung 6)

Silverman *AEC* III.8.1(b): the Weil pairing is antisymmetric,

```
e_n(S, T) · e_n(T, S) = 1,      e_n(S, T) = (e_n(T, S))⁻¹.
```

`EllipticCurves.FunctionField.WeilPairingProductRelation` (`#845`) proves this over an
algebraically closed field with no hypothesis beyond the setting, and
`EllipticCurves.FunctionField.WeilPairingProductRelationMu` (`#855`) lifts it to the value group
`μ_n(F)`.  **This file removes the `[IsAlgClosed F]` from all four of those headlines**, at the cost
of the single hypothesis `hprin` — the principality of `[n]∗((P) − (O))` — and of nothing else.

## Why it is a substitution and not an argument

⚠️ `#845`'s own docstring names its gate exactly, and the sentence is the whole plan of this file:

> **`[IsAlgClosed F]` enters only through the alternating inputs.**

That was written when no alternating headline over a general field existed.  `#899` (PR #359) then
shipped `exists_weilPairingElt_self_eq_one_of_hprin_{two,three}`
(`EllipticCurves.FunctionField.WeilPairingAlternatingBaseChange`), which is the merged `F̄` theorem
**verbatim minus `[IsAlgClosed F]`** — same `hprin`, same conclusion, no hypothesis added.  So the
`F̄`-only input has a general-field replacement of the same shape, and putting it in is the entire
content here.

Everything else in `#845`'s chain was already base-field-agnostic and its file says so:
`exists_divisor_eq_add_sub_single_of_add_eq` (Abel–Jacobi, from `#726`'s class criterion),
`exists_mul_eq_algebraMap_mul` and the generic `exists_prod_eq_of_pullback` all sit **above**
`WeilPairingProductRelation`'s `variable [IsAlgClosed F]` lines.  Nothing here re-proves them.

⚠️ **Nothing about curves is proved in this file.**  Each headline's proof is its `#845` or `#855`
twin's, transcribed, with exactly one edit — `exists_weilPairingElt_self_eq_one_of_isAlgClosed_{two,
three}` becomes `exists_weilPairingElt_self_eq_one_of_hprin_{two,three}` with `hprin` threaded
through.  A reader comparing the two files should find the bodies line-for-line identical
otherwise, and that is the intended way to check this file.

## ⚠️ What is *not* achieved: `hprin` is not discharged, and cannot be by any of this

`hprin` is an **existence** statement, and `#899` recorded the test that decides which
`[IsAlgClosed F]` uses can be removed this way:

> Is the obstruction used to prove an **equality**, or to produce a **witness**?

The alternating inputs are equalities in `F(W)`, so they descend and are gone.  `hprin` produces a
witness, so it does not and will not.  Over `F̄` it is discharged by
`exists_nsmul_divisor_eq_divisor_mulByTwoEndo` (`PullbackPrincipalityTwo`) and
`exists_nsmul_divisor_eq_divisor_mulByThreeEndo` (`PullbackPrincipalityThree`); over a general field
it is open, and it is now the **only** thing between this tree and antisymmetry over an arbitrary
field, exactly as it is on the alternating front.

## The shape of the `hprin` hypothesis, and why it is quantified

`hprin` is **point-local** — it mentions `pointClosedPoint h.left` — while antisymmetry consumes the
alternating property at **three** points: `S`, `T`, and `R = S ⊕ T`.  The hypothesis below is
therefore quantified over all `n`-torsion points rather than taken three times.

⚠️ That is a deliberate strengthening of the hypothesis, and the reason is that it is the exact
signature of the only dischargers that exist: over `F̄` a caller supplies it as the single term
`fun h hm _ hf hd => exists_nsmul_divisor_eq_divisor_mulByTwoEndo h2 h hm hf hd` — which the
`AlgClosedRecovery` block at the bottom of this file exhibits, so the shape is checked and not
merely asserted.  A three-hypothesis variant would be strictly more general and is not built,
because no consumer holds `hprin` at three points without holding it at all of them.  ⚠️ The two
`private` helpers below keep the **point-local** form, so that variant is one `refine` away if that
ever changes.

## Main statements

At `n = 2` and at `n = 3`, in the function field and in `μ_n(F)`:

* `WeierstrassCurve.Affine.exists_weilPairingElt_mul_swap_eq_one_of_hprin_{two,three}` —
  `e_n(S, T) · e_n(T, S) = 1`;
* `WeierstrassCurve.Affine.exists_weilPairingElt_eq_inv_of_hprin_{two,three}` — the quotable form
  `e_n(S, T) = (e_n(T, S))⁻¹`;
* `WeierstrassCurve.Affine.exists_weilPairingMu_mul_swap_eq_one_of_hprin_{two,three}` and
  `WeierstrassCurve.Affine.exists_weilPairingMu_eq_inv_of_hprin_{two,three}` — the same two in the
  value group `rootsOfUnity n F`, where the inverse is the **group** inverse and not a transport of
  the field division of `F(W)`.

On naming: `_two` and `_three` track the **isogeny** — `mulByTwoEndo` versus `mulByThreeEndo` — per
the `## Naming` section of `EllipticCurves.FunctionField.WeilPairing` (`#886`), not the exponent.

On placement: everything is stated in `WeierstrassCurve.Affine`, where the `#845`/`#855` twins live,
with `open CoordinateRing` rather than a nested `namespace`.  ⚠️ `#903`: the build resolves either
spelling from inside a file that opens `CoordinateRing`, so only `#print axioms` on the **fully
qualified** name checks this.

Out of scope: discharging `hprin`; the `∀ g` root-independent headlines of
`EllipticCurves.FunctionField.WeilPairingProductRelationRootIndependent`, whose route is
`weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq` and **not** the alternating property, so lifting
them off `F̄` is a different substitution with a different justification; any edit to `#845`'s or
`#855`'s statements, which are not deprecated — their consumers already carry `[IsAlgClosed F]` and
would gain nothing.

## Non-vacuity

⚠️ The certificate at the bottom is over **`ℚ`**, and it is not the alternating front's certificate
transcribed: it needs three *distinct* rational `2`-torsion points with `S ⊕ T = R`, which
`y² = x³ − x` supplies as `(0, 0)`, `(1, 0)` and `(−1, 0)`.  Over `AlgebraicClosure ℚ` the statement
would be a restatement of `#845`, and over a curve with only one rational `2`-torsion point the
antisymmetry headline would only ever be applied at `S = T`, where it says nothing the alternating
property does not.  `rat_not_isAlgClosed` (`WeilPairingAlternatingBaseChange`) is what makes it
bite.
-/

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

section Two

open Classical in
/-- The rung-5 datum at a `2`-torsion point together with the alternating property for **that**
root, over an arbitrary field: the affine-divisor repackaging of
`exists_weilPairingElt_self_eq_one_of_hprin_two`, and the `_of_hprin` twin of `#845`'s private
`rungFiveAlt_two`.

⚠️ `hprin` is taken here in its **point-local** form, unlike in the headlines below. -/
private lemma rungFiveAltHprin_two (h2 : (2 : F) ≠ 0) {x y : F}
    (h : W.Nonsingular x y) (htors : Point.some x y h ∈ W.torsion 2)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f)) :
    ∃ f g : W.FunctionField, f ≠ 0 ∧ g ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) ∧
      (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
      weilPairingElt h.left g = 1 := by
  obtain ⟨f, hf, hdivproj, g, hg, hu, _, halt⟩ :=
    exists_weilPairingElt_self_eq_one_of_hprin_two h2 h htors hprin
  exact ⟨f, g, hf, hg, divisor_eq_single_of_divisorProj_eq_single_sub_single hdivproj, hu, halt⟩

open Classical in
/-- **Antisymmetry of the Weil pairing at `n = 2` over an arbitrary field**, with `hprin` the only
gate:

```
e_2(S, T) · e_2(T, S) = 1.
```

`exists_weilPairingElt_mul_swap_eq_one_two` (`WeilPairingProductRelation`) is this statement with
`[IsAlgClosed F]` in place of `hprin`; the conclusion is identical and no hypothesis is added.

⚠️ `R = S ⊕ T` is **not** assumed `2`-torsion — `W.torsion 2` is a subgroup, so `hadd ▸
add_mem hmS hmT` derives it — but `hprin` **is** consumed at `R` as well as at `S` and `T`, which
is why it is quantified rather than taken twice. -/
theorem exists_weilPairingElt_mul_swap_eq_one_of_hprin_two (h2 : (2 : F) ≠ 0)
    {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 2) (hmT : Point.some xT yT hT ∈ W.torsion 2)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion 2 →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f)) :
    ∃ gS gT : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 2 = mulByTwoEndo h2 f) ∧
      weilPairingElt hS.left gT * weilPairingElt hT.left gS = 1 := by
  have hmR : Point.some xR yR hR ∈ W.torsion 2 := hadd ▸ add_mem hmS hmT
  obtain ⟨fS, gS, hfS, hgS, hdS, ⟨uS, huS⟩, haltS⟩ := rungFiveAltHprin_two h2 hS hmS (hprin hS hmS)
  obtain ⟨fT, gT, hfT, hgT, hdT, ⟨uT, huT⟩, haltT⟩ := rungFiveAltHprin_two h2 hT hmT (hprin hT hmT)
  obtain ⟨fR, gR, hfR, hgR, hdR, ⟨uR, huR⟩, haltR⟩ := rungFiveAltHprin_two h2 hR hmR (hprin hR hmR)
  obtain ⟨c, k, hc, hk, hprod⟩ :=
    exists_prod_eq_of_pullback (mulByTwoEndo h2) (mulByTwoEndo_algebraMap_base h2)
      two_ne_zero hS hT hR hadd hfS hfT hfR hdS hdT hdR hgS hgT hgR huS huT huR
  have hwR : weilPairingElt hR.left
      (algebraMap F W.FunctionField c * mulByTwoEndo h2 k) = 1 := by
    rw [weilPairingElt_mul, weilPairingElt_algebraMap hR.left hc,
      weilPairingElt_mulByTwoEndo_of_baseField hR.left h2
        (add_self_eq_zero_of_mem_torsion_two hmR) hk, mul_one]
  refine ⟨gS, gT, hgS, hgT, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩, ?_⟩
  exact weilPairingElt_mul_swap_eq_one hS.left hT.left hR.left hadd hgS hgT hprod hwR
    two_ne_zero
    (weilPairingElt_pow_eq_one_of_gS_two_torsion hT.left h2
      (add_self_eq_zero_of_mem_torsion_two hmT) hgS huS)
    haltS haltT haltR

open Classical in
/-- **Antisymmetry at `n = 2` in the quotable inverse form** `e_2(S, T) = (e_2(T, S))⁻¹`, over an
arbitrary field with `hprin` the only gate.  Immediate from the previous theorem; `a * b = 1`
already forces `a = b⁻¹` in a field, so no nonvanishing hypothesis is needed. -/
theorem exists_weilPairingElt_eq_inv_of_hprin_two (h2 : (2 : F) ≠ 0) {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 2) (hmT : Point.some xT yT hT ∈ W.torsion 2)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion 2 →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f)) :
    ∃ gS gT : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 2 = mulByTwoEndo h2 f) ∧
      weilPairingElt hS.left gT = (weilPairingElt hT.left gS)⁻¹ := by
  obtain ⟨gS, gT, hgS, hgT, hcS, hcT, hswap⟩ :=
    exists_weilPairingElt_mul_swap_eq_one_of_hprin_two h2 hS hT hR hmS hmT hadd hprin
  exact ⟨gS, gT, hgS, hgT, hcS, hcT, eq_inv_of_mul_eq_one_left hswap⟩

open Classical in
/-- **Antisymmetry at `n = 2` in `μ_2(F)`, over an arbitrary field** with `hprin` the only gate:

```
μ_2(S, T) · μ_2(T, S) = 1   in rootsOfUnity 2 F.
```

The envelope is the `F(W)`-level theorem's, extended by the two `hpow` data — bound existentially
because `weilPairingMu` is indexed by the *proof*, and produced rather than assumed from the two
rung-5 certificates the envelope already carries. -/
theorem exists_weilPairingMu_mul_swap_eq_one_of_hprin_two (h2 : (2 : F) ≠ 0)
    {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 2) (hmT : Point.some xT yT hT ∈ W.torsion 2)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion 2 →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f)) :
    ∃ gS gT : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 2 = mulByTwoEndo h2 f) ∧
      ∃ hpowST : weilPairingElt hS.left gT ^ 2 = 1,
        ∃ hpowTS : weilPairingElt hT.left gS ^ 2 = 1,
          weilPairingMu hS.left hpowST * weilPairingMu hT.left hpowTS = 1 := by
  obtain ⟨gS, gT, hgS, hgT, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩, hswap⟩ :=
    exists_weilPairingElt_mul_swap_eq_one_of_hprin_two h2 hS hT hR hmS hmT hadd hprin
  have hpowTS : weilPairingElt hT.left gS ^ 2 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_two_torsion hT.left h2
      (add_self_eq_zero_of_mem_torsion_two hmT) hgS huS
  have hpowST : weilPairingElt hS.left gT ^ 2 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_two_torsion hS.left h2
      (add_self_eq_zero_of_mem_torsion_two hmS) hgT huT
  exact ⟨gS, gT, hgS, hgT, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩, hpowST, hpowTS,
    weilPairingMu_mul_swap_eq_one_of_weilPairingElt hS.left hT.left hpowST hpowTS hswap⟩

open Classical in
/-- **Antisymmetry at `n = 2` in `μ_2(F)`, in the quotable inverse form**
`μ_2(S, T) = (μ_2(T, S))⁻¹`, over an arbitrary field with `hprin` the only gate.

The inverse is the **group** inverse of `rootsOfUnity 2 F`, obtained by `eq_inv_of_mul_eq_one_left`
in that group — not a transport of the field division of `F(W)`. -/
theorem exists_weilPairingMu_eq_inv_of_hprin_two (h2 : (2 : F) ≠ 0) {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 2) (hmT : Point.some xT yT hT ∈ W.torsion 2)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion 2 →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f)) :
    ∃ gS gT : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 2 = mulByTwoEndo h2 f) ∧
      ∃ hpowST : weilPairingElt hS.left gT ^ 2 = 1,
        ∃ hpowTS : weilPairingElt hT.left gS ^ 2 = 1,
          weilPairingMu hS.left hpowST = (weilPairingMu hT.left hpowTS)⁻¹ := by
  obtain ⟨gS, gT, hgS, hgT, hcS, hcT, hpowST, hpowTS, hswap⟩ :=
    exists_weilPairingMu_mul_swap_eq_one_of_hprin_two h2 hS hT hR hmS hmT hadd hprin
  exact ⟨gS, gT, hgS, hgT, hcS, hcT, hpowST, hpowTS, eq_inv_of_mul_eq_one_left hswap⟩

end Two

section Three

open Classical in
/-- The rung-5 datum at a `3`-torsion point together with the alternating property for **that**
root, over an arbitrary field: the `n = 3` twin of `rungFiveAltHprin_two`. -/
private lemma rungFiveAltHprin_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x y : F}
    (h : W.Nonsingular x y) (htors : Point.some x y h ∈ W.torsion 3)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f)) :
    ∃ f g : W.FunctionField, f ≠ 0 ∧ g ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) ∧
      (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) ∧
      weilPairingElt h.left g = 1 := by
  obtain ⟨f, hf, hdivproj, g, hg, hu, _, halt⟩ :=
    exists_weilPairingElt_self_eq_one_of_hprin_three h2 h3 h htors hprin
  exact ⟨f, g, hf, hg, divisor_eq_single_of_divisorProj_eq_single_sub_single hdivproj, hu, halt⟩

open Classical in
/-- **Antisymmetry of the Weil pairing at `n = 3` over an arbitrary field**, with `hprin` the only
gate: the `n = 3` twin of `exists_weilPairingElt_mul_swap_eq_one_of_hprin_two`, and
`exists_weilPairingElt_mul_swap_eq_one_three` (`WeilPairingProductRelation`) with `hprin` in place
of `[IsAlgClosed F]`.

⚠️ As at `n = 2`, the `3`-torsion of `R = S ⊕ T` is derived rather than assumed. -/
theorem exists_weilPairingElt_mul_swap_eq_one_of_hprin_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 3) (hmT : Point.some xT yT hT ∈ W.torsion 3)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion 3 →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f)) :
    ∃ gS gT : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 3 = mulByThreeEndo h2 h3 f) ∧
      weilPairingElt hS.left gT * weilPairingElt hT.left gS = 1 := by
  have hmR : Point.some xR yR hR ∈ W.torsion 3 := hadd ▸ add_mem hmS hmT
  obtain ⟨fS, gS, hfS, hgS, hdS, ⟨uS, huS⟩, haltS⟩ :=
    rungFiveAltHprin_three h2 h3 hS hmS (hprin hS hmS)
  obtain ⟨fT, gT, hfT, hgT, hdT, ⟨uT, huT⟩, haltT⟩ :=
    rungFiveAltHprin_three h2 h3 hT hmT (hprin hT hmT)
  obtain ⟨fR, gR, hfR, hgR, hdR, ⟨uR, huR⟩, haltR⟩ :=
    rungFiveAltHprin_three h2 h3 hR hmR (hprin hR hmR)
  obtain ⟨c, k, hc, hk, hprod⟩ :=
    exists_prod_eq_of_pullback (mulByThreeEndo h2 h3) (mulByThreeEndo_algebraMap_base h2 h3)
      three_ne_zero hS hT hR hadd hfS hfT hfR hdS hdT hdR hgS hgT hgR huS huT huR
  have hwR : weilPairingElt hR.left
      (algebraMap F W.FunctionField c * mulByThreeEndo h2 h3 k) = 1 := by
    rw [weilPairingElt_mul, weilPairingElt_algebraMap hR.left hc,
      weilPairingElt_mulByThreeEndo_of_baseField hR.left h2 h3
        (add_add_self_eq_zero_of_mem_torsion_three hmR) hk, mul_one]
  refine ⟨gS, gT, hgS, hgT, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩, ?_⟩
  exact weilPairingElt_mul_swap_eq_one hS.left hT.left hR.left hadd hgS hgT hprod hwR
    three_ne_zero
    (weilPairingElt_pow_eq_one_of_gS_three_baseField hT.left h2 h3
      (add_add_self_eq_zero_of_mem_torsion_three hmT) hgS huS)
    haltS haltT haltR

open Classical in
/-- **Antisymmetry at `n = 3` in the quotable inverse form** `e_3(S, T) = (e_3(T, S))⁻¹`, over an
arbitrary field with `hprin` the only gate. -/
theorem exists_weilPairingElt_eq_inv_of_hprin_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 3) (hmT : Point.some xT yT hT ∈ W.torsion 3)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion 3 →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f)) :
    ∃ gS gT : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 3 = mulByThreeEndo h2 h3 f) ∧
      weilPairingElt hS.left gT = (weilPairingElt hT.left gS)⁻¹ := by
  obtain ⟨gS, gT, hgS, hgT, hcS, hcT, hswap⟩ :=
    exists_weilPairingElt_mul_swap_eq_one_of_hprin_three h2 h3 hS hT hR hmS hmT hadd hprin
  exact ⟨gS, gT, hgS, hgT, hcS, hcT, eq_inv_of_mul_eq_one_left hswap⟩

open Classical in
/-- **Antisymmetry at `n = 3` in `μ_3(F)`, over an arbitrary field** with `hprin` the only gate.
Only the arity of the `hpow` producer differs from the `n = 2` twin,
`weilPairingElt_pow_eq_one_of_gS_three_baseField` in place of
`weilPairingElt_pow_eq_one_of_gS_two_torsion`. -/
theorem exists_weilPairingMu_mul_swap_eq_one_of_hprin_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 3) (hmT : Point.some xT yT hT ∈ W.torsion 3)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion 3 →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f)) :
    ∃ gS gT : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 3 = mulByThreeEndo h2 h3 f) ∧
      ∃ hpowST : weilPairingElt hS.left gT ^ 3 = 1,
        ∃ hpowTS : weilPairingElt hT.left gS ^ 3 = 1,
          weilPairingMu hS.left hpowST * weilPairingMu hT.left hpowTS = 1 := by
  obtain ⟨gS, gT, hgS, hgT, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩, hswap⟩ :=
    exists_weilPairingElt_mul_swap_eq_one_of_hprin_three h2 h3 hS hT hR hmS hmT hadd hprin
  have hpowTS : weilPairingElt hT.left gS ^ 3 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_three_baseField hT.left h2 h3
      (add_add_self_eq_zero_of_mem_torsion_three hmT) hgS huS
  have hpowST : weilPairingElt hS.left gT ^ 3 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_three_baseField hS.left h2 h3
      (add_add_self_eq_zero_of_mem_torsion_three hmS) hgT huT
  exact ⟨gS, gT, hgS, hgT, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩, hpowST, hpowTS,
    weilPairingMu_mul_swap_eq_one_of_weilPairingElt hS.left hT.left hpowST hpowTS hswap⟩

open Classical in
/-- **Antisymmetry at `n = 3` in `μ_3(F)`, in the quotable inverse form**
`μ_3(S, T) = (μ_3(T, S))⁻¹`, over an arbitrary field with `hprin` the only gate. -/
theorem exists_weilPairingMu_eq_inv_of_hprin_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 3) (hmT : Point.some xT yT hT ∈ W.torsion 3)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion 3 →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f)) :
    ∃ gS gT : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 3 = mulByThreeEndo h2 h3 f) ∧
      ∃ hpowST : weilPairingElt hS.left gT ^ 3 = 1,
        ∃ hpowTS : weilPairingElt hT.left gS ^ 3 = 1,
          weilPairingMu hS.left hpowST = (weilPairingMu hT.left hpowTS)⁻¹ := by
  obtain ⟨gS, gT, hgS, hgT, hcS, hcT, hpowST, hpowTS, hswap⟩ :=
    exists_weilPairingMu_mul_swap_eq_one_of_hprin_three h2 h3 hS hT hR hmS hmT hadd hprin
  exact ⟨gS, gT, hgS, hgT, hcS, hcT, hpowST, hpowTS, eq_inv_of_mul_eq_one_left hswap⟩

end Three

/-! ### Recovery of the merged `F̄` headlines

⚠️ These two blocks are the check that the quantified `hprin` above is the **right shape**: over an
algebraically closed field it is discharged by a single term, and what comes out is
`exists_weilPairingElt_mul_swap_eq_one_{two,three}`'s conclusion on the nose.  A hypothesis that no
existing theorem can discharge would look exactly like these statements from the outside, and this
is what distinguishes the two.

They also show that `#845`'s headlines are **subsumed** by this file's.  ⚠️ That is not a reason to
deprecate them: their consumers all carry `[IsAlgClosed F]` already and would gain nothing, and the
`#903` follow-up recorded the same judgement about
`exists_weilPairingElt_self_eq_one_of_algClosed_{two,three}`. -/

section AlgClosedRecovery

variable [IsAlgClosed F]

open Classical in
/-- Over `F̄`, `hprin` is `exists_nsmul_divisor_eq_divisor_mulByTwoEndo` and nothing else, so this
file's `n = 2` headline recovers `exists_weilPairingElt_mul_swap_eq_one_two`. -/
example (h2 : (2 : F) ≠ 0) {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 2) (hmT : Point.some xT yT hT ∈ W.torsion 2)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR) :
    ∃ gS gT : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 2 = mulByTwoEndo h2 f) ∧
      weilPairingElt hS.left gT * weilPairingElt hT.left gS = 1 :=
  exists_weilPairingElt_mul_swap_eq_one_of_hprin_two h2 hS hT hR hmS hmT hadd
    fun h hm _ hf hd => exists_nsmul_divisor_eq_divisor_mulByTwoEndo h2 h hm hf hd

open Classical in
/-- The `n = 3` mirror, recovering `exists_weilPairingElt_mul_swap_eq_one_three` from
`exists_nsmul_divisor_eq_divisor_mulByThreeEndo`. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 3) (hmT : Point.some xT yT hT ∈ W.torsion 3)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR) :
    ∃ gS gT : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 3 = mulByThreeEndo h2 h3 f) ∧
      weilPairingElt hS.left gT * weilPairingElt hT.left gS = 1 :=
  exists_weilPairingElt_mul_swap_eq_one_of_hprin_three h2 h3 hS hT hR hmS hmT hadd
    fun h hm _ hf hd => exists_nsmul_divisor_eq_divisor_mulByThreeEndo h2 h3 h hm hf hd

end AlgClosedRecovery

/-! ### Non-vacuity, over a field that is NOT algebraically closed

⚠️ The base field below is **`ℚ`**, and the certificate needs more than the alternating front's
did.  Antisymmetry is a statement about a *pair* of torsion points, so a curve with a single
rational `2`-torsion point would only ever let the headline be applied at `S = T`, where it says
nothing the alternating property does not.  `y² = x³ − x` has **three** rational `2`-torsion points,
`(0, 0)`, `(1, 0)` and `(−1, 0)`, and `exampleAdd` verifies `(0, 0) ⊕ (1, 0) = (−1, 0)` by Mathlib's
secant formula — so `S`, `T` and `R = S ⊕ T` below are pairwise distinct and all rational.

⚠️ `rat_not_isAlgClosed` (`WeilPairingAlternatingBaseChange`) is what makes this bite: neither
`exists_weilPairingElt_mul_swap_eq_one_two` nor the `AlgClosedRecovery` block above applies to `ℚ`.
-/

section Nonvacuity

private lemma exampleTwo : (2 : ℚ) ≠ 0 := by norm_num

/-! The certificate curve `y² = x³ − x` is the shared `EllipticCurves.Fixture.y2EqX3SubX`, whose
single `[CharZero F]` instance also supplies `IsElliptic` here. -/

open EllipticCurves.Fixture

private lemma exampleNsS : (y2EqX3SubX ℚ).Nonsingular 0 0 :=
  (y2EqX3SubX ℚ).equation_iff_nonsingular.mp (by
    norm_num [y2EqX3SubX, WeierstrassCurve.Affine.equation_iff])

private lemma exampleNsT : (y2EqX3SubX ℚ).Nonsingular 1 0 :=
  (y2EqX3SubX ℚ).equation_iff_nonsingular.mp (by
    norm_num [y2EqX3SubX, WeierstrassCurve.Affine.equation_iff])

private lemma exampleNsR : (y2EqX3SubX ℚ).Nonsingular (-1) 0 :=
  (y2EqX3SubX ℚ).equation_iff_nonsingular.mp (by
    norm_num [y2EqX3SubX, WeierstrassCurve.Affine.equation_iff])

open Classical in
private lemma exampleTorsS : Point.some (0 : ℚ) 0 exampleNsS ∈ (y2EqX3SubX ℚ).torsion 2 :=
  (mem_torsion_two_some_iff exampleNsS).mpr (by norm_num [y2EqX3SubX])

open Classical in
private lemma exampleTorsT : Point.some (1 : ℚ) 0 exampleNsT ∈ (y2EqX3SubX ℚ).torsion 2 :=
  (mem_torsion_two_some_iff exampleNsT).mpr (by norm_num [y2EqX3SubX])

/-- `(0, 0) ⊕ (1, 0) = (−1, 0)` on `y² = x³ − x` over `ℚ`.  The `x`-coordinates differ, so this is
Mathlib's secant case: the slope is `0`, `addX = −1` and `addY = 0`. -/
private lemma exampleAdd : Point.some (0 : ℚ) 0 exampleNsS + Point.some (1 : ℚ) 0 exampleNsT
    = Point.some (-1 : ℚ) 0 exampleNsR := by
  rw [Point.add_of_X_ne (by norm_num)]
  norm_num [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.slope, y2EqX3SubX]

open Classical in
/-- **The `n = 2` antisymmetry headline applies on a curve over `ℚ`**, at two *distinct* rational
`2`-torsion points, with `hprin` the only hypothesis left.

⚠️ **Every `by convert` below is load-bearing, and there are four of them.**  `ℚ` has a genuine
`DecidableEq` instance, so anything stated over `ℚ` is indexed by `instDecidableEqRat`, while the
headline — stated for a general `F` under `open Classical in` — is indexed by
`Classical.propDecidable`.  `Classical.propDecidable` is a *low-priority* local instance, so `open
Classical in` on the `ℚ` lemmas would not change which one they pick: the conversion is unavoidable,
not a stylistic choice.  The objects are propositionally but not syntactically equal and `convert`
closes each gap by `Subsingleton.elim`.

⚠️ It bites in three different places, which is worth naming because only the first is familiar
from this front: the two `torsion` memberships (an `AddSubgroup`), `exampleAdd` (the `Point.instAdd`
inside the `hadd` equation — antisymmetry is the first statement here to take a *group relation*
between torsion points as a hypothesis, so this one is new), and **inside `hprin`**, which is why it
is passed as `fun h hm f hf hd => hprin h (by convert hm) f hf hd` rather than directly.  None of it
arises in the merged non-vacuity blocks on this front, because they all sit over
`AlgebraicClosure ℚ`, which has no decidable equality. -/
example (hprin : ∀ {x y : ℚ} (h : (y2EqX3SubX ℚ).Nonsingular x y),
      Point.some x y h ∈ (y2EqX3SubX ℚ).torsion 2 →
      ∀ f : (y2EqX3SubX ℚ).FunctionField, f ≠ 0 →
        divisor (y2EqX3SubX ℚ) f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) →
        ∃ g₀ : (y2EqX3SubX ℚ).FunctionField, g₀ ≠ 0 ∧
          2 • divisor (y2EqX3SubX ℚ) g₀ = divisor (y2EqX3SubX ℚ) (mulByTwoEndo exampleTwo f)) :
    ∃ gS gT : (y2EqX3SubX ℚ).FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
      (∃ f : (y2EqX3SubX ℚ).FunctionField, f ≠ 0 ∧
        divisor (y2EqX3SubX ℚ) f = Finsupp.single (pointClosedPoint exampleNsS.left) (2 : ℤ) ∧
        ∃ u : (y2EqX3SubX ℚ).CoordinateRingˣ,
          (u : (y2EqX3SubX ℚ).CoordinateRing) • gS ^ 2 = mulByTwoEndo exampleTwo f) ∧
      (∃ f : (y2EqX3SubX ℚ).FunctionField, f ≠ 0 ∧
        divisor (y2EqX3SubX ℚ) f = Finsupp.single (pointClosedPoint exampleNsT.left) (2 : ℤ) ∧
        ∃ u : (y2EqX3SubX ℚ).CoordinateRingˣ,
          (u : (y2EqX3SubX ℚ).CoordinateRing) • gT ^ 2 = mulByTwoEndo exampleTwo f) ∧
      weilPairingElt exampleNsS.left gT * weilPairingElt exampleNsT.left gS = 1 :=
  exists_weilPairingElt_mul_swap_eq_one_of_hprin_two exampleTwo exampleNsS exampleNsT exampleNsR
    (by convert exampleTorsS) (by convert exampleTorsT) (by convert exampleAdd)
    fun h hm f hf hd => hprin h (by convert hm) f hf hd

end Nonvacuity

end WeierstrassCurve.Affine
