/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairingDivisorSlotBilinear

/-!
# Divisor-slot bilinearity over an ARBITRARY field, with `hprin` the only gate (rung 6)

`EllipticCurves.FunctionField.WeilPairingDivisorSlotBilinear` (`#856`) proves that for a fixed
`n`-torsion translation point `P` the Weil pairing is multiplicative in its **divisor** slot,

```
e_n(P, g_R) = e_n(P, g_S) · e_n(P, g_T),      for  S ⊕ T = R,
```

with no hypothesis beyond the setting — over an algebraically closed field.  **This file removes
that `[IsAlgClosed F]` from all four of its headlines**, at the cost of the single hypothesis
`hprin` and of nothing else.

## Where the instance came from, which is the only question that mattered

⚠️ `#856` names its own gate, in its own docstring, and the sentence is the whole plan of this file:

> `[IsAlgClosed F]` enters only through `exists_gS_{two,three}_of_isAlgClosed` (`#791`/`#825`), that
> is, only through `hprin`.

That is checkable and was checked: `grep -n IsAlgClosed` over `#856` returns two
`variable [IsAlgClosed F]` lines and six uses, all of them the rung-5 producer applied at `S`, `T`
and `R` inside the two `weilPairingElt` headlines.  The two `weilPairingMu` headlines call it
nowhere — they consume the `weilPairingElt` ones.

The replacement is `exists_gS_{two,three}` itself
(`EllipticCurves.FunctionField.NthRootOfPullback`), which is stated over an **arbitrary** field and
takes `hprin`; `EllipticCurves.FunctionField.PullbackPrincipalityTwo` derives the `F̄` corollary
from it in one term.  So the edit is six call sites,
`exists_gS_two_of_isAlgClosed h2 hS hmS` ↦ `exists_gS_two h2 hS hmS (hprin hS hmS)`, and each body
is otherwise its `#856` twin's transcribed.  ⚠️ **Nothing about curves is proved here.**

⚠️ **No second instance is incurred, and this is the one place the trade could have been bad.**
`exists_gS_two` carries `[IsDedekindDomain W.CoordinateRing]`, which reads like swapping one gate
for another, but `EllipticCurves.FunctionField.CoordinateRingNormalGeneral` registers
`instIsDedekindDomain` for *any* elliptic curve over *any* field, so it is discharged by instance
search; and its `[DecidableEq F]` is handled by the `open Classical in` the twins already carry.
Neither appears in any statement below.

## ⚠️ What is *not* achieved

`hprin` is not discharged and cannot be by any of this.  `#899` recorded the test that decides which
`[IsAlgClosed F]` uses can be removed this way:

> Is the obstruction used to prove an **equality**, or to produce a **witness**?

`hprin` produces a witness, so it does not descend.  Over `F̄` it is discharged by
`exists_nsmul_divisor_eq_divisor_mulByTwoEndo` and `exists_nsmul_divisor_eq_divisor_mulByThreeEndo`;
over a general field it is open, and with this file it is the only thing between this tree and the
whole of rung 6 over an arbitrary field — alternating (`#899`), antisymmetry with roots produced
(`#907`) and supplied (`#910`), and now bilinearity.

## On the name shape

The names below are the twin's with `_of_hprin` appended, so `…_divisorSlot_add_two_of_hprin`, the
index staying where `#856` puts it.  ⚠️ This is deliberate and is the first file written after the
review of `#910` settled the rule on the record: **"mirror your twin" wins while every `_of_hprin`
file has a twin**, because the only reader who cares where the qualifier sits is the one holding
the two statements side by side.  `#907` writes `…_of_hprin_two` for the same reason — its twin
`#845` puts the index last — so the two spellings are a consequence of the rule and not drift.

## Main statements

At `n = 2` and `n = 3`, in the function field and in `μ_n(F)`:

* `WeierstrassCurve.Affine.exists_weilPairingElt_divisorSlot_add_{two,three}_of_hprin`;
* `WeierstrassCurve.Affine.exists_weilPairingMu_divisorSlot_add_{two,three}_of_hprin`.

⚠️ As in `#856`, `P` is a **fourth** point, a priori independent of `S`, `T` and `R`, and its
`n`-torsion is genuinely needed — it is what makes `e_n(P, c · [n]∗k) = 1`.  `R`'s torsion is
**derived** from `hadd` and never assumed.  In the `μ_n(F)` statements the three `hpow` data are
produced rather than assumed, from the rung-5 certificates the envelope already carries.

On placement: everything is in `WeierstrassCurve.Affine`, with `open CoordinateRing` rather than a
nested `namespace`.  ⚠️ `#903`: only `#print axioms` on the **fully qualified** name checks that.

## Non-vacuity, and why this file has a `ℚ` block where `#910` has none

`#910` skipped its certificate deliberately, because its headlines take `f_S`, `f_T`, `g_S`, `g_T`
and their rung-5 certificates as *hypotheses*, so a block could only have restated them.  **These
headlines take no root data at all** — their hypotheses are `h2`, four nonsingular points, three
torsion memberships and `hadd` — so over `ℚ` everything but `hprin` is discharged concretely, and
the block demonstrates exactly the claim the title makes.  Both `n` are certified below, over `ℚ`
itself and not over `AlgebraicClosure ℚ`, which is where `#856`'s own certificates live.

Out of scope: discharging `hprin`; any edit to `#856`'s, `#845`'s or `#855`'s statements, none of
which are deprecated — their consumers carry `[IsAlgClosed F]` already and gain nothing;
`WeilPairingDivisorSlotHom`'s bundled `weilPairingMuHom`, which wants a `hpow` datum uniform in the
slot variable and is a different statement; non-degeneracy; Ward; rung 4.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(a).
-/

namespace WeierstrassCurve.Affine

open CoordinateRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

section Two

open Classical in
/-- **Divisor-slot bilinearity at `n = 2` over an arbitrary field**, with `hprin` the only gate:

```
e_2(P, g_R) = e_2(P, g_S) · e_2(P, g_T),     for  S ⊕ T = R.
```

`exists_weilPairingElt_divisorSlot_add_two` (`WeilPairingDivisorSlotBilinear`) is this statement
with `[IsAlgClosed F]` in place of `hprin`; the conclusion is identical and no other hypothesis is
added.  The three roots are produced together with their rung-5 certificates, and the root at `R`
is **exposed**, because divisor-slot bilinearity is a statement about it.

⚠️ No alternating property is consumed, at any of the four points — that is `#856`'s finding, not a
new one, and it is why this lift needs nothing from `#899`. -/
theorem exists_weilPairingElt_divisorSlot_add_two_of_hprin (h2 : (2 : F) ≠ 0)
    {xP yP xS yS xT yT xR yR : F} (hP : W.Nonsingular xP yP) (hS : W.Nonsingular xS yS)
    (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmP : Point.some xP yP hP ∈ W.torsion 2) (hmS : Point.some xS yS hS ∈ W.torsion 2)
    (hmT : Point.some xT yT hT ∈ W.torsion 2)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion 2 →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f)) :
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
  obtain ⟨fS, hfS, hdS, gS, hgS, uS, huS⟩ := exists_gS_two h2 hS hmS (hprin hS hmS)
  obtain ⟨fT, hfT, hdT, gT, hgT, uT, huT⟩ := exists_gS_two h2 hT hmT (hprin hT hmT)
  obtain ⟨fR, hfR, hdR, gR, hgR, uR, huR⟩ := exists_gS_two h2 hR hmR (hprin hR hmR)
  obtain ⟨c, k, hc, hk, hprod⟩ :=
    exists_prod_eq_of_pullback (mulByTwoEndo h2) (mulByTwoEndo_algebraMap_base h2)
      two_ne_zero hS hT hR hadd hfS hfT hfR hdS hdT hdR hgS hgT hgR huS huT huR
  have htorsP := add_self_eq_zero_of_mem_torsion_two hmP
  exact ⟨gS, gT, gR, hgS, hgT, hgR, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩,
    ⟨fR, hfR, hdR, uR, huR⟩,
    weilPairingElt_divisorSlot_add_two hP.left h2 htorsP hc hk hprod⟩

open Classical in
/-- **Divisor-slot bilinearity at `n = 2` in `μ_n(F)`, over an arbitrary field** with `hprin` the
only gate.

The envelope is `exists_weilPairingElt_divisorSlot_add_two_of_hprin`'s, extended by the three `hpow`
data: they are bound existentially because `weilPairingMu` is indexed by the *proof*, and they are
**produced** — not assumed — from the three rung-5 certificates the envelope already carries, by
`weilPairingElt_pow_eq_one_of_gS_two_torsion` (`TranslationTorsion`) applied at `P` with each root.

⚠️ The `μ_n` index `n` is free and is not tied to the `2`-torsion of the four points; that is
`#856`'s arrangement, unchanged. -/
theorem exists_weilPairingMu_divisorSlot_add_two_of_hprin (h2 : (2 : F) ≠ 0)
    {xP yP xS yS xT yT xR yR : F} (hP : W.Nonsingular xP yP) (hS : W.Nonsingular xS yS)
    (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmP : Point.some xP yP hP ∈ W.torsion 2) (hmS : Point.some xS yS hS ∈ W.torsion 2)
    (hmT : Point.some xT yT hT ∈ W.torsion 2)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion 2 →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f)) :
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
      exists_weilPairingElt_divisorSlot_add_two_of_hprin h2 hP hS hT hR hmP hmS hmT hadd hprin
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

open Classical in
/-- **Divisor-slot bilinearity at `n = 3` over an arbitrary field**, with `hprin` the only gate: the
`n = 3` mirror of `exists_weilPairingElt_divisorSlot_add_two_of_hprin`, and
`exists_weilPairingElt_divisorSlot_add_three` with `hprin` in place of `[IsAlgClosed F]`.  Only the
pullback differs from the `n = 2` twin, `mulByThreeEndo h2 h3` for `mulByTwoEndo h2`, and with it
the rung-5 producer `exists_gS_three` and the discharge of the correction factor. -/
theorem exists_weilPairingElt_divisorSlot_add_three_of_hprin (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xP yP xS yS xT yT xR yR : F} (hP : W.Nonsingular xP yP) (hS : W.Nonsingular xS yS)
    (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmP : Point.some xP yP hP ∈ W.torsion 3) (hmS : Point.some xS yS hS ∈ W.torsion 3)
    (hmT : Point.some xT yT hT ∈ W.torsion 3)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion 3 →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f)) :
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
  obtain ⟨fS, hfS, hdS, gS, hgS, uS, huS⟩ := exists_gS_three h2 h3 hS hmS (hprin hS hmS)
  obtain ⟨fT, hfT, hdT, gT, hgT, uT, huT⟩ := exists_gS_three h2 h3 hT hmT (hprin hT hmT)
  obtain ⟨fR, hfR, hdR, gR, hgR, uR, huR⟩ := exists_gS_three h2 h3 hR hmR (hprin hR hmR)
  obtain ⟨c, k, hc, hk, hprod⟩ :=
    exists_prod_eq_of_pullback (mulByThreeEndo h2 h3) (mulByThreeEndo_algebraMap_base h2 h3)
      three_ne_zero hS hT hR hadd hfS hfT hfR hdS hdT hdR hgS hgT hgR huS huT huR
  have htorsP := add_add_self_eq_zero_of_mem_torsion_three hmP
  exact ⟨gS, gT, gR, hgS, hgT, hgR, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩,
    ⟨fR, hfR, hdR, uR, huR⟩,
    weilPairingElt_divisorSlot_add_three hP.left h2 h3 htorsP hc hk hprod⟩

open Classical in
/-- **Divisor-slot bilinearity at `n = 3` in `μ_n(F)`, over an arbitrary field** with `hprin` the
only gate.  The `n = 3` mirror of `exists_weilPairingMu_divisorSlot_add_two_of_hprin`; the three
`hpow` data come from `weilPairingElt_pow_eq_one_of_gS_three_baseField` (`TranslationTriplingComm`)
in place of `weilPairingElt_pow_eq_one_of_gS_two_torsion`. -/
theorem exists_weilPairingMu_divisorSlot_add_three_of_hprin (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xP yP xS yS xT yT xR yR : F} (hP : W.Nonsingular xP yP) (hS : W.Nonsingular xS yS)
    (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmP : Point.some xP yP hP ∈ W.torsion 3) (hmS : Point.some xS yS hS ∈ W.torsion 3)
    (hmT : Point.some xT yT hT ∈ W.torsion 3)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion 3 →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f)) :
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
      exists_weilPairingElt_divisorSlot_add_three_of_hprin h2 h3 hP hS hT hR hmP hmS hmT hadd hprin
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

/-! ### Recovery of the merged `F̄` headlines

⚠️ These two blocks are the check that the quantified `hprin` is the **right shape**: a hypothesis
that nothing can discharge looks exactly like these statements from the outside.  Over an
algebraically closed field it is discharged by a single term, and what comes out is
`exists_weilPairingElt_divisorSlot_add_{two,three}`'s statement on the nose.

`#907` made this block standard for `_of_hprin`-style weakenings on this front; it is four lines and
it is the difference between a theorem and a plausible-looking vacuity. -/

section AlgClosedRecovery

variable [IsAlgClosed F]

open Classical in
/-- Over `F̄`, `hprin` is `exists_nsmul_divisor_eq_divisor_mulByTwoEndo` and nothing else, so the
`n = 2` headline recovers `exists_weilPairingElt_divisorSlot_add_two`. -/
example (h2 : (2 : F) ≠ 0) {xP yP xS yS xT yT xR yR : F} (hP : W.Nonsingular xP yP)
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
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
      weilPairingElt hP.left gR = weilPairingElt hP.left gS * weilPairingElt hP.left gT :=
  exists_weilPairingElt_divisorSlot_add_two_of_hprin h2 hP hS hT hR hmP hmS hmT hadd
    fun h hm _ hf hd => exists_nsmul_divisor_eq_divisor_mulByTwoEndo h2 h hm hf hd

open Classical in
/-- The `n = 3` mirror, recovering `exists_weilPairingElt_divisorSlot_add_three` from
`exists_nsmul_divisor_eq_divisor_mulByThreeEndo`. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {xP yP xS yS xT yT xR yR : F}
    (hP : W.Nonsingular xP yP) (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT)
    (hR : W.Nonsingular xR yR)
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
      weilPairingElt hP.left gR = weilPairingElt hP.left gS * weilPairingElt hP.left gT :=
  exists_weilPairingElt_divisorSlot_add_three_of_hprin h2 h3 hP hS hT hR hmP hmS hmT hadd
    fun h hm _ hf hd => exists_nsmul_divisor_eq_divisor_mulByThreeEndo h2 h3 h hm hf hd

end AlgClosedRecovery

/-! ### Non-vacuity, over a field that is NOT algebraically closed

⚠️ The base field below is **`ℚ`**, and this is where the file departs from `#910`, which
deliberately shipped no certificate.  `#910`'s headlines take the roots and their rung-5
certificates as *hypotheses*, so a block there could only have restated them.  These headlines take
**no root data at all** — `h2`, four nonsingular points, three torsion memberships and `hadd` — so
over `ℚ` every hypothesis but `hprin` is discharged concretely, and each certificate below
restates the headline's conclusion **in full**, rung-5 conjuncts included.  ⚠️ `#856`'s own
certificates live over `AlgebraicClosure ℚ`, where `AlgClosedRecovery` already applies; these do
not.

⚠️ **"In full" is load-bearing, and it was a repair.**  These four certificates originally
`obtain`ed the headline and then projected, restating only
`∃ gS gT gR, e_n(P, g_R) = e_n(P, g_S) · e_n(P, g_T)` — and *that* statement is proved by
`⟨1, 1, 1, by rw [weilPairingElt_one, one_mul]⟩` with **no hypothesis at all**, since
`weilPairingElt_one` (`WeilPairingAntisymmetricMu`) gives `e_n(P, 1) = 1`.  The proof was doing real
work — the elaborator did discharge every hypothesis but `hprin` at concrete `ℚ` data — but the
*statement* did not record it, so nothing stopped a later edit from swapping in the trivial term and
leaving the file green.

> **The test, before shipping any `ℚ` non-vacuity block: can `⟨1, 1, 1, by simp⟩` prove your
> statement?**  If it can, the block is decorative in exactly the way `#910`'s standard warns
> against, however genuine the proof behind it is.  Restate the headline's conclusion in full; never
> `obtain`-and-project.

⚠️ At `n = 2` the curve `y² = x³ − x` has **three** distinct rational `2`-torsion points and
`exampleAdd` verifies `(0, 0) ⊕ (1, 0) = (−1, 0)` by Mathlib's secant formula, so `S`, `T` and `R`
are pairwise distinct.  The translation point is `P = S`: the curve has no fourth `2`-torsion point
to name and `P` is a free variable of the headline.  At `n = 3` on `y² + y = x³` the only nameable
`3`-torsion points are `(0, 0)` and its negative `(0, −1)`, so `P = S = T = (0, 0)` and
`R = (0, −1)` is forced — the limitation is `#856`'s, inherited and stated rather than repaired.

⚠️ **Every `by convert` below is load-bearing, and there are twenty — five per certificate.**
`ℚ` has a genuine `DecidableEq` instance, so anything stated over `ℚ` is indexed by
`instDecidableEqRat`, while the headlines — stated for a general `F` under `open Classical in` —
are indexed by `Classical.propDecidable`.  The latter is a *low-priority local* instance, so
`open Classical in` on the `ℚ` lemmas does **not** change which one they pick; the conversion is
unavoidable rather than stylistic, and `convert` closes each gap by `Subsingleton.elim`.  Deleting
all twenty is not a tidy-up: it is eight elaboration errors.  They sit in three kinds of place —
the **three** `torsion` memberships (`P` has its own, which is what makes it five here and not
`#907`'s four), the `Point.instAdd` inside `hadd`, and **inside `hprin`**, which is why it is
passed as `fun h hm f hf hd => hprin h (by convert hm) f hf hd`. -/

section Nonvacuity

private lemma exampleTwo : (2 : ℚ) ≠ 0 := by norm_num

private lemma exampleThree : (3 : ℚ) ≠ 0 := by norm_num

/-- The curve `y² = x³ − x` over `ℚ`, of discriminant `64`. -/
private noncomputable def exampleCurve : Affine ℚ := ⟨0, 0, 0, -1, 0⟩

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
private lemma exampleTorsS : Point.some (0 : ℚ) 0 exampleNsS ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNsS).mpr (by norm_num [exampleCurve])

open Classical in
private lemma exampleTorsT : Point.some (1 : ℚ) 0 exampleNsT ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNsT).mpr (by norm_num [exampleCurve])

/-- `(0, 0) ⊕ (1, 0) = (−1, 0)` on `y² = x³ − x` over `ℚ`.  The `x`-coordinates differ, so this is
Mathlib's secant case: the slope is `0`, `addX = −1` and `addY = 0`. -/
private lemma exampleAdd : Point.some (0 : ℚ) 0 exampleNsS + Point.some (1 : ℚ) 0 exampleNsT
    = Point.some (-1 : ℚ) 0 exampleNsR := by
  rw [Point.add_of_X_ne (by norm_num)]
  norm_num [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.slope, exampleCurve]

open Classical in
/-- **Divisor-slot bilinearity at `n = 2` applies on a curve over `ℚ`**, at three *distinct*
rational `2`-torsion points, with `hprin` the only hypothesis left. -/
example (hprin : ∀ {x y : ℚ} (h : exampleCurve.Nonsingular x y),
      Point.some x y h ∈ exampleCurve.torsion 2 →
      ∀ f : exampleCurve.FunctionField, f ≠ 0 →
        divisor exampleCurve f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) →
        ∃ g₀ : exampleCurve.FunctionField, g₀ ≠ 0 ∧
          2 • divisor exampleCurve g₀
            = divisor exampleCurve (mulByTwoEndo exampleTwo f)) :
    ∃ gS gT gR : exampleCurve.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧ gR ≠ 0 ∧
      (∃ f : exampleCurve.FunctionField, f ≠ 0 ∧
        divisor exampleCurve f = Finsupp.single (pointClosedPoint exampleNsS.left) (2 : ℤ) ∧
        ∃ u : exampleCurve.CoordinateRingˣ,
          (u : exampleCurve.CoordinateRing) • gS ^ 2 = mulByTwoEndo exampleTwo f) ∧
      (∃ f : exampleCurve.FunctionField, f ≠ 0 ∧
        divisor exampleCurve f = Finsupp.single (pointClosedPoint exampleNsT.left) (2 : ℤ) ∧
        ∃ u : exampleCurve.CoordinateRingˣ,
          (u : exampleCurve.CoordinateRing) • gT ^ 2 = mulByTwoEndo exampleTwo f) ∧
      (∃ f : exampleCurve.FunctionField, f ≠ 0 ∧
        divisor exampleCurve f = Finsupp.single (pointClosedPoint exampleNsR.left) (2 : ℤ) ∧
        ∃ u : exampleCurve.CoordinateRingˣ,
          (u : exampleCurve.CoordinateRing) • gR ^ 2 = mulByTwoEndo exampleTwo f) ∧
      weilPairingElt exampleNsS.left gR
        = weilPairingElt exampleNsS.left gS * weilPairingElt exampleNsS.left gT :=
  exists_weilPairingElt_divisorSlot_add_two_of_hprin exampleTwo exampleNsS exampleNsS exampleNsT
    exampleNsR (by convert exampleTorsS) (by convert exampleTorsS) (by convert exampleTorsT)
    (by convert exampleAdd) fun h hm f hf hd => hprin h (by convert hm) f hf hd

open Classical in
/-- **Divisor-slot bilinearity at `n = 2` in `μ_2(ℚ)`, on a curve over `ℚ`.**  ⚠️ The three `hpow`
data are produced inside the headline from its own rung-5 certificates, so they are not an extra
burden on the caller; they are bound here because `weilPairingMu` is indexed by them. -/
example (hprin : ∀ {x y : ℚ} (h : exampleCurve.Nonsingular x y),
      Point.some x y h ∈ exampleCurve.torsion 2 →
      ∀ f : exampleCurve.FunctionField, f ≠ 0 →
        divisor exampleCurve f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) →
        ∃ g₀ : exampleCurve.FunctionField, g₀ ≠ 0 ∧
          2 • divisor exampleCurve g₀
            = divisor exampleCurve (mulByTwoEndo exampleTwo f)) :
    ∃ gS gT gR : exampleCurve.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧ gR ≠ 0 ∧
      (∃ f : exampleCurve.FunctionField, f ≠ 0 ∧
        divisor exampleCurve f = Finsupp.single (pointClosedPoint exampleNsS.left) (2 : ℤ) ∧
        ∃ u : exampleCurve.CoordinateRingˣ,
          (u : exampleCurve.CoordinateRing) • gS ^ 2 = mulByTwoEndo exampleTwo f) ∧
      (∃ f : exampleCurve.FunctionField, f ≠ 0 ∧
        divisor exampleCurve f = Finsupp.single (pointClosedPoint exampleNsT.left) (2 : ℤ) ∧
        ∃ u : exampleCurve.CoordinateRingˣ,
          (u : exampleCurve.CoordinateRing) • gT ^ 2 = mulByTwoEndo exampleTwo f) ∧
      (∃ f : exampleCurve.FunctionField, f ≠ 0 ∧
        divisor exampleCurve f = Finsupp.single (pointClosedPoint exampleNsR.left) (2 : ℤ) ∧
        ∃ u : exampleCurve.CoordinateRingˣ,
          (u : exampleCurve.CoordinateRing) • gR ^ 2 = mulByTwoEndo exampleTwo f) ∧
      ∃ hpowS : weilPairingElt exampleNsS.left gS ^ 2 = 1,
        ∃ hpowT : weilPairingElt exampleNsS.left gT ^ 2 = 1,
          ∃ hpowR : weilPairingElt exampleNsS.left gR ^ 2 = 1,
            weilPairingMu exampleNsS.left hpowR
              = weilPairingMu exampleNsS.left hpowS * weilPairingMu exampleNsS.left hpowT :=
  exists_weilPairingMu_divisorSlot_add_two_of_hprin exampleTwo exampleNsS exampleNsS exampleNsT
    exampleNsR (by convert exampleTorsS) (by convert exampleTorsS) (by convert exampleTorsT)
    (by convert exampleAdd) fun h hm f hf hd => hprin h (by convert hm) f hf hd

/-- The curve `y² + y = x³` over `ℚ`, of discriminant `−27`. -/
private noncomputable def exampleCurveThree : Affine ℚ := ⟨0, 0, 1, 0, 0⟩

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
private lemma exampleTorsThreeS :
    Point.some (0 : ℚ) 0 exampleNsThreeS ∈ exampleCurveThree.torsion 3 :=
  mem_torsion_three_some_iff'.mpr (by
    norm_num [exampleCurveThree, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈])

open Classical in
/-- `(0, 0) ⊕ (0, 0) = (0, −1)` on `y² + y = x³` over `ℚ`: doubling the named `3`-torsion point
gives its negative, which is the other one. -/
private lemma exampleAddThree :
    Point.some (0 : ℚ) 0 exampleNsThreeS + Point.some (0 : ℚ) 0 exampleNsThreeS
      = Point.some (0 : ℚ) (-1) exampleNsThreeR := by
  rw [Point.add_of_Y_ne (by norm_num [exampleCurveThree, WeierstrassCurve.Affine.negY])]
  simp only [Point.some.injEq]
  norm_num [exampleCurveThree, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.negY]

open Classical in
/-- **Divisor-slot bilinearity at `n = 3` applies on a curve over `ℚ`**, with `hprin` the only
hypothesis left.  ⚠️ Here `P = S = T = (0, 0)` and `R = (0, −1)`; see the section docstring for why
no other `3`-torsion point of `y² + y = x³` is nameable. -/
example (hprin : ∀ {x y : ℚ} (h : exampleCurveThree.Nonsingular x y),
      Point.some x y h ∈ exampleCurveThree.torsion 3 →
      ∀ f : exampleCurveThree.FunctionField, f ≠ 0 →
        divisor exampleCurveThree f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) →
        ∃ g₀ : exampleCurveThree.FunctionField, g₀ ≠ 0 ∧
          3 • divisor exampleCurveThree g₀
            = divisor exampleCurveThree (mulByThreeEndo exampleTwo exampleThree f)) :
    ∃ gS gT gR : exampleCurveThree.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧ gR ≠ 0 ∧
      (∃ f : exampleCurveThree.FunctionField, f ≠ 0 ∧
        divisor exampleCurveThree f
          = Finsupp.single (pointClosedPoint exampleNsThreeS.left) (3 : ℤ) ∧
        ∃ u : exampleCurveThree.CoordinateRingˣ,
          (u : exampleCurveThree.CoordinateRing) • gS ^ 3
            = mulByThreeEndo exampleTwo exampleThree f) ∧
      (∃ f : exampleCurveThree.FunctionField, f ≠ 0 ∧
        divisor exampleCurveThree f
          = Finsupp.single (pointClosedPoint exampleNsThreeS.left) (3 : ℤ) ∧
        ∃ u : exampleCurveThree.CoordinateRingˣ,
          (u : exampleCurveThree.CoordinateRing) • gT ^ 3
            = mulByThreeEndo exampleTwo exampleThree f) ∧
      (∃ f : exampleCurveThree.FunctionField, f ≠ 0 ∧
        divisor exampleCurveThree f
          = Finsupp.single (pointClosedPoint exampleNsThreeR.left) (3 : ℤ) ∧
        ∃ u : exampleCurveThree.CoordinateRingˣ,
          (u : exampleCurveThree.CoordinateRing) • gR ^ 3
            = mulByThreeEndo exampleTwo exampleThree f) ∧
      weilPairingElt exampleNsThreeS.left gR
        = weilPairingElt exampleNsThreeS.left gS * weilPairingElt exampleNsThreeS.left gT :=
  exists_weilPairingElt_divisorSlot_add_three_of_hprin exampleTwo exampleThree exampleNsThreeS
    exampleNsThreeS exampleNsThreeS exampleNsThreeR (by convert exampleTorsThreeS)
    (by convert exampleTorsThreeS) (by convert exampleTorsThreeS) (by convert exampleAddThree)
    fun h hm f hf hd => hprin h (by convert hm) f hf hd

open Classical in
/-- **Divisor-slot bilinearity at `n = 3` in `μ_3(ℚ)`, on a curve over `ℚ`.**  ⚠️ Here
`P = S = T = (0, 0)`; see the section docstring. -/
example (hprin : ∀ {x y : ℚ} (h : exampleCurveThree.Nonsingular x y),
      Point.some x y h ∈ exampleCurveThree.torsion 3 →
      ∀ f : exampleCurveThree.FunctionField, f ≠ 0 →
        divisor exampleCurveThree f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) →
        ∃ g₀ : exampleCurveThree.FunctionField, g₀ ≠ 0 ∧
          3 • divisor exampleCurveThree g₀
            = divisor exampleCurveThree (mulByThreeEndo exampleTwo exampleThree f)) :
    ∃ gS gT gR : exampleCurveThree.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧ gR ≠ 0 ∧
      (∃ f : exampleCurveThree.FunctionField, f ≠ 0 ∧
        divisor exampleCurveThree f
          = Finsupp.single (pointClosedPoint exampleNsThreeS.left) (3 : ℤ) ∧
        ∃ u : exampleCurveThree.CoordinateRingˣ,
          (u : exampleCurveThree.CoordinateRing) • gS ^ 3
            = mulByThreeEndo exampleTwo exampleThree f) ∧
      (∃ f : exampleCurveThree.FunctionField, f ≠ 0 ∧
        divisor exampleCurveThree f
          = Finsupp.single (pointClosedPoint exampleNsThreeS.left) (3 : ℤ) ∧
        ∃ u : exampleCurveThree.CoordinateRingˣ,
          (u : exampleCurveThree.CoordinateRing) • gT ^ 3
            = mulByThreeEndo exampleTwo exampleThree f) ∧
      (∃ f : exampleCurveThree.FunctionField, f ≠ 0 ∧
        divisor exampleCurveThree f
          = Finsupp.single (pointClosedPoint exampleNsThreeR.left) (3 : ℤ) ∧
        ∃ u : exampleCurveThree.CoordinateRingˣ,
          (u : exampleCurveThree.CoordinateRing) • gR ^ 3
            = mulByThreeEndo exampleTwo exampleThree f) ∧
      ∃ hpowS : weilPairingElt exampleNsThreeS.left gS ^ 3 = 1,
        ∃ hpowT : weilPairingElt exampleNsThreeS.left gT ^ 3 = 1,
          ∃ hpowR : weilPairingElt exampleNsThreeS.left gR ^ 3 = 1,
            weilPairingMu exampleNsThreeS.left hpowR
              = weilPairingMu exampleNsThreeS.left hpowS
                  * weilPairingMu exampleNsThreeS.left hpowT :=
  exists_weilPairingMu_divisorSlot_add_three_of_hprin exampleTwo exampleThree exampleNsThreeS
    exampleNsThreeS exampleNsThreeS exampleNsThreeR (by convert exampleTorsThreeS)
    (by convert exampleTorsThreeS) (by convert exampleTorsThreeS) (by convert exampleAddThree)
    fun h hm f hf hd => hprin h (by convert hm) f hf hd

end Nonvacuity

end WeierstrassCurve.Affine
