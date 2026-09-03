/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.CoordinateRingNormalGeneral
import EllipticCurves.FunctionField.MulByNXCoordFormula
import EllipticCurves.FunctionField.WeilPairingDivisorSlotBilinearHprin
import EllipticCurves.FunctionField.WeilPairingTranslationSlotHprinN

/-!
# Divisor-slot bilinearity at an ARBITRARY `n`, with `hprin` the only gate (rung 6)

`EllipticCurves.FunctionField.WeilPairingDivisorSlotBilinearHprin` (`#918`) proves that for a fixed
torsion translation point `P` the Weil pairing is multiplicative in its **divisor** slot,

```
e_n(P, g_R) = e_n(P, g_S) · e_n(P, g_T),      for  S ⊕ T = R,
```

over an arbitrary field with `hprin` the only gate — at `n = 2` and `n = 3`.  This file states the
same four headlines at **every** `n`, and discharges the one new side condition at every `3`-smooth
`n`.  It is the divisor-slot counterpart of what `#1308`
(`EllipticCurves.FunctionField.WeilPairingTranslationSlotHprinN`) did for the translation slot.

## ⚠️ The restriction to `n = 2, 3` was chronological, not mathematical — and it stopped being so
## twelve hours ago

Strip the numerals from `exists_weilPairingElt_divisorSlot_add_two_of_hprin` and
`…_three_of_hprin` and the two proof bodies are the same five steps.  Of the seven inputs those
steps use, **six were already general** when this file was written and **two of the six became
general on 2026-08-31**:

| input the `n = 2` body uses | general-`n` form |
| --- | --- |
| `exists_gS_two` | `exists_gS_n` (`NthRootOfPullbackN`, `#1304`) |
| `exists_prod_eq_of_pullback (mulByTwoEndo h2) …` | **already general** — `φ`, `n` parameters |
| `mulByTwoEndo_algebraMap_base` | `mulByNEndo_algebraMap_base` (`MulByNPullback`) |
| `add_self_eq_zero_of_mem_torsion_two hmP` | `mem_torsion_iff.mp hmP` |
| `weilPairingElt_divisorSlot_add_two` | **missing — supplied below** |
| `weilPairingElt_pow_eq_one_of_gS_two_torsion` | `…_of_gS_n_torsion` (`#1308`) |
| `weilPairingMu_divisorSlot_add_of_weilPairingElt` | **already general** |

⚠️ `exists_prod_eq_of_pullback` (`WeilPairingProductRelation`, `#845`) says so in its own docstring
— *"a future divisor-level `[n]∗` (`#403`/`#405`) instantiates it unchanged"* — and that is exactly
what happens here: `φ := mulByNEndo n hn`.  **Nothing in this file needs `ωₙ`**, Ward, rung 4 or
`#251`; `mulByNEndo` comes from the group law on the generic point (`#1165`/PR #436), not from the
division-polynomial coordinates.

## The one new brick, and why it lives here

`EllipticCurves.FunctionField.WeilPairingAntisymmetric` proves that the classical correction factor
`c · ([n]∗f)` is invisible to the pairing — but only at `n = 2` and `n = 3`
(`weilPairingElt_mulByTwoEndo{,_of_baseField}` and the `mulByThreeEndo` mirror).  Its general-`n`
input has existed for days (`translateEndo_mulByNEndo_apply_torsion{,_of_baseField}`,
`TranslationMulByNCommGeneral`, `#1013`), so `weilPairingElt_mulByNEndo` and
`weilPairingElt_divisorSlot_add_n` below are transcriptions of the merged `n = 2` proofs.

⚠️ **They are here and not in `WeilPairingAntisymmetric`.**  That file sits *below*
`MulByNPullback`/`TranslationMulByNCommGeneral` in the import graph — it is imported by the whole
Weil-pairing front — and moving these three declarations into it would push the generic-point stack
underneath every one of its consumers for the sake of three lemmas that only this file uses.

## ⚠️ This does NOT subsume the merged `_two` / `_three` headlines

`mulByNEndo` is built from the generic point and so carries `[W.IsElliptic]`.  The merged
`_of_hprin` statements carry `[W.IsElliptic]` too — so unlike `#1304`, whose hypothesis sets were
genuinely *incomparable*, the trade here is favourable and the general form really is stronger.
**They are still not deprecated, restated or touched**, for `#1304`'s and `#1308`'s reason: they are
the right thing to cite at `n = 2, 3`, their proofs do not route through the generic point, and the
`Recovery` block below is what certifies that nothing is lost.  Nothing in this file edits
`WeilPairingDivisorSlotBilinearHprin.lean`.

## Main statements

* `WeierstrassCurve.Affine.CoordinateRing.weilPairingElt_mulByNEndo` and
  `…_of_baseField` — a `[n]∗`-pullback contributes `1`, at every `n`.
* `WeierstrassCurve.Affine.CoordinateRing.weilPairingElt_divisorSlot_add_n` — divisor-slot
  bilinearity with the classical correction factor `c · [n]∗f`, at every `n`.
* `WeierstrassCurve.Affine.exists_weilPairingElt_divisorSlot_add_n_of_hprin` and
  `…exists_weilPairingMu_divisorSlot_add_n_of_hprin` — the two headlines at an arbitrary `n`, in the
  function field and in `μ_n(F)`.
* `…_of_smooth_of_hprin` for each, with the non-constancy hypothesis discharged at every `3`-smooth
  `n ≠ 0`.  ⚠️ Those two do not reach `n = 5`: the argument manufactures no new prime.
* `…_of_ne_zero_of_hprin` for each — **the same at every `n` with `(n : F) ≠ 0`** (`#1549`), the
  transcendence coming from `transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`
  (`EllipticCurves.FunctionField.MulByNXCoordFormula`).  ⚠️ `n = 5` and `n = 10` are here, and the
  `_of_smooth` pair is a corollary — compiled in the `example` beside them, not asserted.

As in `#861`/`#918`, `P` is a **fourth** point, a priori independent of `S`, `T` and `R`, and its
`n`-torsion is what makes `e_n(P, c · [n]∗k) = 1`.  `R`'s torsion is **derived** from `hadd` and
never assumed.

## On the name shape

`_n` sits where `#918` puts `_two` and `_three`, and `_of_hprin` stays last — the *"mirror your
twin"* rule the review of `#907` settled, applied to the file this one generalises.

## Non-vacuity

Two blocks, answering different questions.

* `Recovery` derives all four merged headlines from the general ones through
  `mulByNEndo_two` / `mulByNEndo_three`.  All four are `private`: public copies would duplicate
  merged names.
* `Nonvacuity` instantiates the `3`-smooth corollaries at **`n = 4`** over **`ℚ`**, an index no
  merged rung-5 or rung-6 divisor-slot statement reaches and a field that is not algebraically
  closed, so neither `#861`'s headlines nor `#918`'s `AlgClosedRecovery` block applies to it.
  ⚠️ `hprin` remains a hypothesis there, exactly as at `n = 2, 3`; the certificate says the *other*
  hypotheses are inhabited at a new index and claims nothing more.

Out of scope: discharging `hprin` — it produces a *witness*, and `#899`'s test says witnesses do not
descend; any edit to `#861`'s, `#918`'s or `#845`'s statements; non-degeneracy, which carries a
second independent `[IsAlgClosed F]` through `card_torsion_two` and is not a lift; Ward; rung 4.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(a).
-/

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic] {xT yT : F}

/-! ### The correction factor `c · [n]∗f` contributes `1`, at every `n` -/

/-- **A `[n]∗`-pullback contributes `1`, for an `n`-torsion translation point.**  The general-`n`
form of `weilPairingElt_mulByTwoEndo` (`WeilPairingAntisymmetric`):
`translateEndo_mulByNEndo_apply_torsion` says `τ_T∗` fixes `[n]∗f` outright whenever `n • 𝒯_T = 0`,
and a fixed nonzero element has pairing value `1`. -/
theorem weilPairingElt_mulByNEndo (hT : W.Equation xT yT) (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (htors : n • translatePoint hT = 0) {f : W.FunctionField} (hf : f ≠ 0) :
    weilPairingElt hT (mulByNEndo n hn f) = 1 :=
  (weilPairingElt_eq_one_iff_translateEndo_fixed hT
    (fun hz => hf (mulByNEndo_injective n hn (by rw [hz, map_zero])))).mpr
      (translateEndo_mulByNEndo_apply_torsion hT n hn htors f)

open Classical in
/-- **A `[n]∗`-pullback contributes `1`, from the base-field `n`-torsion of `T`.**  The
`torsionPoint` form of `weilPairingElt_mulByNEndo`, transporting `n • T = 0` in `W.Point` through
`translatePoint_nsmul_eq_zero` — the uniform transport, at every `n`. -/
theorem weilPairingElt_mulByNEndo_of_baseField (hT : W.Equation xT yT) (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (htors : n • torsionPoint hT = 0) {f : W.FunctionField} (hf : f ≠ 0) :
    weilPairingElt hT (mulByNEndo n hn f) = 1 :=
  weilPairingElt_mulByNEndo hT n hn (translatePoint_nsmul_eq_zero hT htors) hf

open Classical in
/-- **Divisor-slot bilinearity at every `n`, with the classical correction factor.**  The
general-`n` form of `weilPairingElt_divisorSlot_add_two`: `w = c · [n]∗f` is exactly the shape
Silverman's `g_{S ⊕ T} = c · g_S · g_T · (h ∘ [n])` produces, and it is exactly the shape
`exists_prod_eq_of_pullback` returns, so `hw` costs nothing at the call site. -/
theorem weilPairingElt_divisorSlot_add_n (hT : W.Equation xT yT) (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (htors : n • torsionPoint hT = 0)
    {gS gT gR f : W.FunctionField} {c : F} (hc : c ≠ 0) (hf : f ≠ 0)
    (hprod : gR = gS * gT * (algebraMap F W.FunctionField c * mulByNEndo n hn f)) :
    weilPairingElt hT gR = weilPairingElt hT gS * weilPairingElt hT gT :=
  weilPairingElt_divisorSlot_add hT hprod <| by
    rw [weilPairingElt_mul, weilPairingElt_algebraMap hT hc,
      weilPairingElt_mulByNEndo_of_baseField hT n hn htors hf, mul_one]

end CoordinateRing

open CoordinateRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-! ### The two headlines at an arbitrary `n` -/

open Classical in
/-- **Divisor-slot bilinearity at an arbitrary `n` over an arbitrary field**, with `hprin` the only
gate:

```
e_n(P, g_R) = e_n(P, g_S) · e_n(P, g_T),     for  S ⊕ T = R.
```

`exists_weilPairingElt_divisorSlot_add_two_of_hprin` (`#918`) with the numeral removed:
`exists_gS_two` becomes `exists_gS_n`, `mulByTwoEndo h2` becomes `mulByNEndo n hn`, and
`weilPairingElt_divisorSlot_add_two` becomes `weilPairingElt_divisorSlot_add_n`.  The product
relation step `exists_prod_eq_of_pullback` was already stated at an arbitrary `n` and an arbitrary
pullback.

⚠️ `hprin` is quantified over the *point*, because roots are needed at all three of `S`, `T` and
`R` — that is `#918`'s shape, not a new one, and it is why this headline's `hprin` differs from the
translation slot's point-local one.  The three roots are produced together with their rung-5
certificates, and the root at `R` is **exposed**, because divisor-slot bilinearity is a statement
about it.

⚠️ No alternating property is consumed, at any of the four points — `#861`'s finding, unchanged. -/
theorem exists_weilPairingElt_divisorSlot_add_n_of_hprin {n : ℕ}
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) (hnz : n ≠ 0)
    {xP yP xS yS xT yT xR yR : F} (hP : W.Nonsingular xP yP) (hS : W.Nonsingular xS yS)
    (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmP : Point.some xP yP hP ∈ W.torsion n) (hmS : Point.some xS yS hS ∈ W.torsion n)
    (hmT : Point.some xT yT hT ∈ W.torsion n)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion n →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          n • divisor W g₀ = divisor W (mulByNEndo n hn f)) :
    ∃ gS gT gR : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧ gR ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n = mulByNEndo n hn f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ n = mulByNEndo n hn f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hR.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gR ^ n = mulByNEndo n hn f) ∧
      weilPairingElt hP.left gR = weilPairingElt hP.left gS * weilPairingElt hP.left gT := by
  have hmR : Point.some xR yR hR ∈ W.torsion n := hadd ▸ add_mem hmS hmT
  obtain ⟨fS, hfS, hdS, gS, hgS, uS, huS⟩ := exists_gS_n hn hS hmS (hprin hS hmS)
  obtain ⟨fT, hfT, hdT, gT, hgT, uT, huT⟩ := exists_gS_n hn hT hmT (hprin hT hmT)
  obtain ⟨fR, hfR, hdR, gR, hgR, uR, huR⟩ := exists_gS_n hn hR hmR (hprin hR hmR)
  obtain ⟨c, k, hc, hk, hprod⟩ :=
    exists_prod_eq_of_pullback (mulByNEndo n hn) (mulByNEndo_algebraMap_base n hn)
      hnz hS hT hR hadd hfS hfT hfR hdS hdT hdR hgS hgT hgR huS huT huR
  exact ⟨gS, gT, gR, hgS, hgT, hgR, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩,
    ⟨fR, hfR, hdR, uR, huR⟩,
    weilPairingElt_divisorSlot_add_n hP.left n hn (mem_torsion_iff.mp hmP) hc hk hprod⟩

open Classical in
/-- **Divisor-slot bilinearity at an arbitrary `n` in `μ_n(F)`, over an arbitrary field** with
`hprin` the only gate.

The envelope is `exists_weilPairingElt_divisorSlot_add_n_of_hprin`'s, extended by the three `hpow`
data: they are bound existentially because `weilPairingMu` is indexed by the *proof*, and they are
**produced** — not assumed — from the three rung-5 certificates the envelope already carries, by
`weilPairingElt_pow_eq_one_of_gS_n_torsion` (`#1308`) applied at `P` with each root.

⚠️ `[NeZero n]` replaces the `hnz : n ≠ 0` of the `F(W)`-level headline, and the asymmetry is forced
rather than chosen: `weilPairingMu` occurs in the **statement** and needs the instance to elaborate,
so it cannot be produced inside the proof.  `NeZero.ne n` recovers `n ≠ 0`.

⚠️ The `μ_n` exponent is the *same* `n` as the isogeny here, unlike in
`weilPairingElt_pow_eq_one_of_gS_n_torsion`, where the two indices are genuinely independent; that
is `#861`'s arrangement for this family, unchanged. -/
theorem exists_weilPairingMu_divisorSlot_add_n_of_hprin {n : ℕ} [NeZero n]
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    {xP yP xS yS xT yT xR yR : F} (hP : W.Nonsingular xP yP) (hS : W.Nonsingular xS yS)
    (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmP : Point.some xP yP hP ∈ W.torsion n) (hmS : Point.some xS yS hS ∈ W.torsion n)
    (hmT : Point.some xT yT hT ∈ W.torsion n)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion n →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          n • divisor W g₀ = divisor W (mulByNEndo n hn f)) :
    ∃ gS gT gR : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧ gR ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n = mulByNEndo n hn f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ n = mulByNEndo n hn f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hR.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gR ^ n = mulByNEndo n hn f) ∧
      ∃ hpowS : weilPairingElt hP.left gS ^ n = 1,
        ∃ hpowT : weilPairingElt hP.left gT ^ n = 1,
          ∃ hpowR : weilPairingElt hP.left gR ^ n = 1,
            weilPairingMu hP.left hpowR
              = weilPairingMu hP.left hpowS * weilPairingMu hP.left hpowT := by
  obtain ⟨gS, gT, gR, hgS, hgT, hgR, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩,
    ⟨fR, hfR, hdR, uR, huR⟩, hbil⟩ :=
      exists_weilPairingElt_divisorSlot_add_n_of_hprin hn (NeZero.ne n) hP hS hT hR hmP hmS hmT
        hadd hprin
  have htorsP := mem_torsion_iff.mp hmP
  have hpowS : weilPairingElt hP.left gS ^ n = 1 :=
    weilPairingElt_pow_eq_one_of_gS_n_torsion hP.left n hn htorsP hgS huS
  have hpowT : weilPairingElt hP.left gT ^ n = 1 :=
    weilPairingElt_pow_eq_one_of_gS_n_torsion hP.left n hn htorsP hgT huT
  have hpowR : weilPairingElt hP.left gR ^ n = 1 :=
    weilPairingElt_pow_eq_one_of_gS_n_torsion hP.left n hn htorsP hgR huR
  exact ⟨gS, gT, gR, hgS, hgT, hgR, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩,
    ⟨fR, hfR, hdR, uR, huR⟩, hpowS, hpowT, hpowR,
    weilPairingMu_divisorSlot_add_of_weilPairingElt hP.left hpowS hpowT hpowR hbil⟩

/-! ### The two headlines at every `3`-smooth `n`, with the non-constancy hypothesis discharged -/

open Classical in
/-- **Divisor-slot bilinearity at every `3`-smooth `n ≠ 0`, with `hprin` the only hypothesis beyond
the setting.**  `exists_weilPairingElt_divisorSlot_add_n_of_hprin` with `hn` discharged by
`transcendental_xCoord_nsmul_of_smooth`.

⚠️ **This statement** does not cover `n = 5`: the argument that supplies its transcendence
manufactures no new prime.  ⚠️ **The file does** — `…_of_ne_zero_of_hprin` below is the same
conclusion at every `n` with `(n : F) ≠ 0`, and this one is a corollary of it.  It is kept as an
independent route: its transcendence consumes no division polynomial. -/
theorem exists_weilPairingElt_divisorSlot_add_of_smooth_of_hprin (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {n : ℕ} (hnz : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    {xP yP xS yS xT yT xR yR : F} (hP : W.Nonsingular xP yP) (hS : W.Nonsingular xS yS)
    (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmP : Point.some xP yP hP ∈ W.torsion n) (hmS : Point.some xS yS hS ∈ W.torsion n)
    (hmT : Point.some xT yT hT ∈ W.torsion n)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion n →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          n • divisor W g₀ =
            divisor W (mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hnz hfac) f)) :
    ∃ gS gT gR : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧ gR ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hnz hfac) f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hnz hfac) f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hR.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gR ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hnz hfac) f) ∧
      weilPairingElt hP.left gR = weilPairingElt hP.left gS * weilPairingElt hP.left gT :=
  exists_weilPairingElt_divisorSlot_add_n_of_hprin _ hnz hP hS hT hR hmP hmS hmT hadd hprin


open Classical in
/-- **Additivity of the Weil-pairing element in the divisor slot at every `n` with `(n : F) ≠ 0`**
— `exists_weilPairingElt_divisorSlot_add_n_of_hprin` with `hn` discharged by
`transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`
(`EllipticCurves.FunctionField.MulByNXCoordFormula`) instead of by the `3`-smooth degree tower.

⚠️ **`n = 5` and `n = 10` are here.**  The `example` at the end of this section derives the
`3`-smooth statement from this one verbatim; the `_of_smooth` form is kept as an independent
route. -/
theorem exists_weilPairingElt_divisorSlot_add_of_ne_zero_of_hprin (h2 : (2 : F) ≠ 0)
    {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    {xP yP xS yS xT yT xR yR : F} (hP : W.Nonsingular xP yP) (hS : W.Nonsingular xS yS)
    (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmP : Point.some xP yP hP ∈ W.torsion n) (hmS : Point.some xS yS hS ∈ W.torsion n)
    (hmT : Point.some xT yT hT ∈ W.torsion n)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion n →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          n • divisor W g₀ =
            divisor W (mulByNEndo n
              (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn) f)) :
    ∃ gS gT gR : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧ gR ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn) f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn) f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hR.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gR ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn) f) ∧
      weilPairingElt hP.left gR = weilPairingElt hP.left gS * weilPairingElt hP.left gT :=
  exists_weilPairingElt_divisorSlot_add_n_of_hprin _ (by rintro rfl; simp at hn) hP hS hT hR
    hmP hmS hmT hadd hprin

open Classical in
/-- **`…_of_smooth` is a corollary of `…_of_ne_zero`** — its statement verbatim, proved from the
general layer, so the containment between the two layers is compiled rather than asserted.  ⚠️ The
two `mulByNEndo` terms carry *different* transcendence proofs and match only because
`Transcendental` is a `Prop`; `EllipticCurves.FunctionField.MulByNDegreeGeneral` records that trap
at its own `:72-76`. -/
example (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {n : ℕ} (hnz : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    {xP yP xS yS xT yT xR yR : F} (hP : W.Nonsingular xP yP) (hS : W.Nonsingular xS yS)
    (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmP : Point.some xP yP hP ∈ W.torsion n) (hmS : Point.some xS yS hS ∈ W.torsion n)
    (hmT : Point.some xT yT hT ∈ W.torsion n)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion n →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          n • divisor W g₀ =
            divisor W (mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hnz hfac) f)) :
    ∃ gS gT gR : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧ gR ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hnz hfac) f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hnz hfac) f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hR.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gR ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hnz hfac) f) ∧
      weilPairingElt hP.left gR = weilPairingElt hP.left gS * weilPairingElt hP.left gT :=
  exists_weilPairingElt_divisorSlot_add_of_ne_zero_of_hprin h2
    (Nat.intCast_ne_zero_of_smooth h2 h3 hnz hfac) hP hS hT hR hmP hmS hmT hadd hprin

open Classical in
/-- **Divisor-slot bilinearity in `μ_n(F)` at every `3`-smooth `n ≠ 0`.**  The `μ` mirror of
`exists_weilPairingElt_divisorSlot_add_of_smooth_of_hprin`.

⚠️ `[NeZero n]` here where the `F(W)`-level sibling takes `hnz : n ≠ 0`; the reason is the
general-`n` headline's, and it is forced. -/
theorem exists_weilPairingMu_divisorSlot_add_of_smooth_of_hprin (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {n : ℕ} [NeZero n] (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    {xP yP xS yS xT yT xR yR : F} (hP : W.Nonsingular xP yP) (hS : W.Nonsingular xS yS)
    (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmP : Point.some xP yP hP ∈ W.torsion n) (hmS : Point.some xS yS hS ∈ W.torsion n)
    (hmT : Point.some xT yT hT ∈ W.torsion n)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion n →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          n • divisor W g₀ = divisor W
            (mulByNEndo n
              (transcendental_xCoord_nsmul_of_smooth h2 h3 (NeZero.ne n) hfac) f)) :
    ∃ gS gT gR : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧ gR ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 (NeZero.ne n) hfac) f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 (NeZero.ne n) hfac) f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hR.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gR ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 (NeZero.ne n) hfac) f) ∧
      ∃ hpowS : weilPairingElt hP.left gS ^ n = 1,
        ∃ hpowT : weilPairingElt hP.left gT ^ n = 1,
          ∃ hpowR : weilPairingElt hP.left gR ^ n = 1,
            weilPairingMu hP.left hpowR
              = weilPairingMu hP.left hpowS * weilPairingMu hP.left hpowT :=
  exists_weilPairingMu_divisorSlot_add_n_of_hprin _ hP hS hT hR hmP hmS hmT hadd hprin

open Classical in
/-- **Additivity of the `μ_n`-valued pairing in the divisor slot at every `n` with `(n : F) ≠ 0`**
— the `weilPairingMu` companion of the theorem above, by the same substitution. -/
theorem exists_weilPairingMu_divisorSlot_add_of_ne_zero_of_hprin (h2 : (2 : F) ≠ 0)
    {n : ℕ} [NeZero n] (hn : ((n : ℤ) : F) ≠ 0)
    {xP yP xS yS xT yT xR yR : F} (hP : W.Nonsingular xP yP) (hS : W.Nonsingular xS yS)
    (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmP : Point.some xP yP hP ∈ W.torsion n) (hmS : Point.some xS yS hS ∈ W.torsion n)
    (hmT : Point.some xT yT hT ∈ W.torsion n)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion n →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          n • divisor W g₀ = divisor W
            (mulByNEndo n
              (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn) f)) :
    ∃ gS gT gR : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧ gR ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn) f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn) f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hR.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gR ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn) f) ∧
      ∃ hpowS : weilPairingElt hP.left gS ^ n = 1,
        ∃ hpowT : weilPairingElt hP.left gT ^ n = 1,
          ∃ hpowR : weilPairingElt hP.left gR ^ n = 1,
            weilPairingMu hP.left hpowR
              = weilPairingMu hP.left hpowS * weilPairingMu hP.left hpowT :=
  exists_weilPairingMu_divisorSlot_add_n_of_hprin _ hP hS hT hR hmP hmS hmT hadd hprin

/-! ### Recovery of the four merged headlines

⚠️ Each statement below is its merged twin **verbatim**, and each is proved *through* the general
form rather than re-proved.  This is the check that distinguishes a faithful generalisation from a
new statement that resembles one; the elaborator does it, so no reader has to take *"the proofs are
the merged proofs with the numeral removed"* on faith.

⚠️ All four are `private`: public copies would duplicate merged names. -/

section Recovery

open Classical in
/-- `exists_weilPairingElt_divisorSlot_add_two_of_hprin`, recovered.

⚠️ `Nat.cast_ofNat` is not decoration: the general form writes the divisor coefficient as
`((2 : ℕ) : ℤ)` and the merged statement writes `(2 : ℤ)`, so without it **both** the hypothesis and
the conclusion fail to match. -/
private theorem exists_weilPairingElt_divisorSlot_add_two_of_general (h2 : (2 : F) ≠ 0)
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
  have key := exists_weilPairingElt_divisorSlot_add_n_of_hprin
    (transcendental_xCoord_two_nsmul (W := W) h2) two_ne_zero hP hS hT hR hmP hmS hmT hadd
    (by intro x y h hm; simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using hprin h hm)
  simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using key

open Classical in
/-- `exists_weilPairingElt_divisorSlot_add_three_of_hprin`, recovered, through
`mulByNEndo_three`. -/
private theorem exists_weilPairingElt_divisorSlot_add_three_of_general (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {xP yP xS yS xT yT xR yR : F} (hP : W.Nonsingular xP yP)
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
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
  have key := exists_weilPairingElt_divisorSlot_add_n_of_hprin
    (transcendental_xCoord_three_nsmul (W := W) h2 h3) three_ne_zero hP hS hT hR hmP hmS hmT hadd
    (by intro x y h hm; simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using hprin h hm)
  simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using key

open Classical in
/-- `exists_weilPairingMu_divisorSlot_add_two_of_hprin`, recovered. -/
private theorem exists_weilPairingMu_divisorSlot_add_two_of_general (h2 : (2 : F) ≠ 0)
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
  have key := exists_weilPairingMu_divisorSlot_add_n_of_hprin
    (transcendental_xCoord_two_nsmul (W := W) h2) hP hS hT hR hmP hmS hmT hadd
    (by intro x y h hm; simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using hprin h hm)
  simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using key

open Classical in
/-- `exists_weilPairingMu_divisorSlot_add_three_of_hprin`, recovered. -/
private theorem exists_weilPairingMu_divisorSlot_add_three_of_general (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {xP yP xS yS xT yT xR yR : F} (hP : W.Nonsingular xP yP)
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
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
  have key := exists_weilPairingMu_divisorSlot_add_n_of_hprin
    (transcendental_xCoord_three_nsmul (W := W) h2 h3) hP hS hT hR hmP hmS hmT hadd
    (by intro x y h hm; simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using hprin h hm)
  simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using key

end Recovery

/-! ### Non-vacuity at `n = 4`, over `ℚ`

⚠️ The base field is **`ℚ`**, which is not algebraically closed, so neither `#861`'s headlines nor
`#918`'s `AlgClosedRecovery` block applies to it — and `n = 4` is an index no merged rung-5 or
rung-6 divisor-slot statement reaches at all.

`y² = x³ − x` has three rational `2`-torsion points `(0, 0)`, `(1, 0)`, `(−1, 0)`; each is
`4`-torsion because `4 • X = 2 • (2 • X)`, and `exampleAdd` verifies `(0, 0) ⊕ (1, 0) = (−1, 0)` by
Mathlib's secant formula.  So `S`, `T`, `R` are named, distinct and rational; the fourth point `P`
is taken to be `S`.

⚠️ `hprin` remains a hypothesis here, exactly as it does at `n = 2, 3` over a general field.  What
these certificates establish is that every *other* hypothesis — `3`-smoothness at a composite index,
the elliptic instance, non-singularity, `n`-torsion at four points and the group relation between
three of them — is inhabited outside `{2, 3}`. -/

section Nonvacuity

private lemma exampleTwo : (2 : ℚ) ≠ 0 := by norm_num

private lemma exampleThree : (3 : ℚ) ≠ 0 := by norm_num

/-- `4` is `3`-smooth.  ⚠️ Not `by decide`: the `Decidable` instance for the bounded quantifier over
`primeFactors` gets stuck (`#1213`).  This is `NthRootOfPullbackN`'s `primeFactors_four` idiom. -/
private lemma primeFactorsFour : ∀ p ∈ (4 : ℕ).primeFactors, p = 2 ∨ p = 3 := by
  intro p hp
  obtain ⟨hpp, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
  rw [show (4 : ℕ) = 2 ^ 2 from rfl] at hdvd
  exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow hdvd))

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
private lemma exampleTorTwoS : Point.some (0 : ℚ) 0 exampleNsS ∈ (y2EqX3SubX ℚ).torsion 2 :=
  (mem_torsion_two_some_iff exampleNsS).mpr (by norm_num [y2EqX3SubX])

open Classical in
private lemma exampleTorTwoT : Point.some (1 : ℚ) 0 exampleNsT ∈ (y2EqX3SubX ℚ).torsion 2 :=
  (mem_torsion_two_some_iff exampleNsT).mpr (by norm_num [y2EqX3SubX])

open Classical in
private lemma exampleTorTwoR : Point.some (-1 : ℚ) 0 exampleNsR ∈ (y2EqX3SubX ℚ).torsion 2 :=
  (mem_torsion_two_some_iff exampleNsR).mpr (by norm_num [y2EqX3SubX])

open Classical in
/-- `(0, 0)` is `4`-torsion because it is `2`-torsion: `4 • X = 2 • (2 • X)`. -/
private lemma exampleTorFourS : Point.some (0 : ℚ) 0 exampleNsS ∈ (y2EqX3SubX ℚ).torsion 4 := by
  rw [mem_torsion_iff, show (4 : ℕ) = 2 * 2 from rfl, mul_nsmul,
    mem_torsion_iff.mp exampleTorTwoS, smul_zero]

open Classical in
private lemma exampleTorFourT : Point.some (1 : ℚ) 0 exampleNsT ∈ (y2EqX3SubX ℚ).torsion 4 := by
  rw [mem_torsion_iff, show (4 : ℕ) = 2 * 2 from rfl, mul_nsmul,
    mem_torsion_iff.mp exampleTorTwoT, smul_zero]

open Classical in
private lemma exampleTorFourR : Point.some (-1 : ℚ) 0 exampleNsR ∈ (y2EqX3SubX ℚ).torsion 4 := by
  rw [mem_torsion_iff, show (4 : ℕ) = 2 * 2 from rfl, mul_nsmul,
    mem_torsion_iff.mp exampleTorTwoR, smul_zero]

/-- `(0, 0) ⊕ (1, 0) = (−1, 0)` on `y² = x³ − x` over `ℚ`.  The `x`-coordinates differ, so this is
Mathlib's secant case: the slope is `0`, `addX = −1` and `addY = 0`. -/
private lemma exampleAdd : Point.some (0 : ℚ) 0 exampleNsS + Point.some (1 : ℚ) 0 exampleNsT
    = Point.some (-1 : ℚ) 0 exampleNsR := by
  rw [Point.add_of_X_ne (by norm_num)]
  norm_num [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.slope, y2EqX3SubX]

open Classical in
/-- **Divisor-slot bilinearity applies at `n = 4` on a curve over `ℚ`**, at three distinct rational
`4`-torsion divisor points, with `hprin` the only hypothesis left.

⚠️ **Every `by convert` is load-bearing.**  `ℚ` has a genuine `DecidableEq` instance, so anything
stated over `ℚ` is indexed by `instDecidableEqRat`, while the headline — stated for a general `F`
under `open Classical in` — is indexed by `Classical.propDecidable`, a *low-priority* local
instance.  The objects are propositionally but not syntactically equal and `convert` closes each gap
by `Subsingleton.elim`.  It bites in the `torsion` memberships and in the `Point.instAdd` inside
`hadd`; ⚠️ unlike the translation-slot mirror it bites **inside `hprin` too**, because this family's
`hprin` is quantified over `n`-torsion points rather than being point-local. -/
example (hprin : ∀ {x y : ℚ} (h : (y2EqX3SubX ℚ).Nonsingular x y),
      Point.some x y h ∈ (y2EqX3SubX ℚ).torsion 4 →
      ∀ f : (y2EqX3SubX ℚ).FunctionField, f ≠ 0 →
        divisor (y2EqX3SubX ℚ) f = Finsupp.single (pointClosedPoint h.left) (4 : ℤ) →
        ∃ g₀ : (y2EqX3SubX ℚ).FunctionField, g₀ ≠ 0 ∧
          4 • divisor (y2EqX3SubX ℚ) g₀ = divisor (y2EqX3SubX ℚ) (mulByNEndo 4
            (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree (by norm_num)
              primeFactorsFour) f)) :
    ∃ gS gT gR : (y2EqX3SubX ℚ).FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧ gR ≠ 0 ∧
      (∃ f : (y2EqX3SubX ℚ).FunctionField, f ≠ 0 ∧
        divisor (y2EqX3SubX ℚ) f = Finsupp.single (pointClosedPoint exampleNsS.left) (4 : ℤ) ∧
        ∃ u : (y2EqX3SubX ℚ).CoordinateRingˣ, (u : (y2EqX3SubX ℚ).CoordinateRing) • gS ^ 4
          = mulByNEndo 4 (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree
              (by norm_num) primeFactorsFour) f) ∧
      (∃ f : (y2EqX3SubX ℚ).FunctionField, f ≠ 0 ∧
        divisor (y2EqX3SubX ℚ) f = Finsupp.single (pointClosedPoint exampleNsT.left) (4 : ℤ) ∧
        ∃ u : (y2EqX3SubX ℚ).CoordinateRingˣ, (u : (y2EqX3SubX ℚ).CoordinateRing) • gT ^ 4
          = mulByNEndo 4 (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree
              (by norm_num) primeFactorsFour) f) ∧
      (∃ f : (y2EqX3SubX ℚ).FunctionField, f ≠ 0 ∧
        divisor (y2EqX3SubX ℚ) f = Finsupp.single (pointClosedPoint exampleNsR.left) (4 : ℤ) ∧
        ∃ u : (y2EqX3SubX ℚ).CoordinateRingˣ, (u : (y2EqX3SubX ℚ).CoordinateRing) • gR ^ 4
          = mulByNEndo 4 (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree
              (by norm_num) primeFactorsFour) f) ∧
      weilPairingElt exampleNsS.left gR
        = weilPairingElt exampleNsS.left gS * weilPairingElt exampleNsS.left gT := by
  refine exists_weilPairingElt_divisorSlot_add_of_smooth_of_hprin exampleTwo exampleThree
    (n := 4) (by norm_num) primeFactorsFour exampleNsS exampleNsS exampleNsT exampleNsR
    (by convert exampleTorFourS) (by convert exampleTorFourS) (by convert exampleTorFourT)
    (by convert exampleAdd) ?_
  intro x y h hm
  simpa only [Nat.cast_ofNat] using hprin h (by convert hm)

open Classical in
/-- **The `μ_4(ℚ)`-valued form applies at `n = 4` too**, with the three `hpow` data produced rather
than assumed. -/
example (hprin : ∀ {x y : ℚ} (h : (y2EqX3SubX ℚ).Nonsingular x y),
      Point.some x y h ∈ (y2EqX3SubX ℚ).torsion 4 →
      ∀ f : (y2EqX3SubX ℚ).FunctionField, f ≠ 0 →
        divisor (y2EqX3SubX ℚ) f = Finsupp.single (pointClosedPoint h.left) (4 : ℤ) →
        ∃ g₀ : (y2EqX3SubX ℚ).FunctionField, g₀ ≠ 0 ∧
          4 • divisor (y2EqX3SubX ℚ) g₀ = divisor (y2EqX3SubX ℚ) (mulByNEndo 4
            (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree (by norm_num)
              primeFactorsFour) f)) :
    ∃ gS gT gR : (y2EqX3SubX ℚ).FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧ gR ≠ 0 ∧
      (∃ f : (y2EqX3SubX ℚ).FunctionField, f ≠ 0 ∧
        divisor (y2EqX3SubX ℚ) f = Finsupp.single (pointClosedPoint exampleNsS.left) (4 : ℤ) ∧
        ∃ u : (y2EqX3SubX ℚ).CoordinateRingˣ, (u : (y2EqX3SubX ℚ).CoordinateRing) • gS ^ 4
          = mulByNEndo 4 (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree
              (by norm_num) primeFactorsFour) f) ∧
      (∃ f : (y2EqX3SubX ℚ).FunctionField, f ≠ 0 ∧
        divisor (y2EqX3SubX ℚ) f = Finsupp.single (pointClosedPoint exampleNsT.left) (4 : ℤ) ∧
        ∃ u : (y2EqX3SubX ℚ).CoordinateRingˣ, (u : (y2EqX3SubX ℚ).CoordinateRing) • gT ^ 4
          = mulByNEndo 4 (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree
              (by norm_num) primeFactorsFour) f) ∧
      (∃ f : (y2EqX3SubX ℚ).FunctionField, f ≠ 0 ∧
        divisor (y2EqX3SubX ℚ) f = Finsupp.single (pointClosedPoint exampleNsR.left) (4 : ℤ) ∧
        ∃ u : (y2EqX3SubX ℚ).CoordinateRingˣ, (u : (y2EqX3SubX ℚ).CoordinateRing) • gR ^ 4
          = mulByNEndo 4 (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree
              (by norm_num) primeFactorsFour) f) ∧
      ∃ hpowS : weilPairingElt exampleNsS.left gS ^ 4 = 1,
        ∃ hpowT : weilPairingElt exampleNsS.left gT ^ 4 = 1,
          ∃ hpowR : weilPairingElt exampleNsS.left gR ^ 4 = 1,
            weilPairingMu exampleNsS.left hpowR
              = weilPairingMu exampleNsS.left hpowS * weilPairingMu exampleNsS.left hpowT := by
  refine exists_weilPairingMu_divisorSlot_add_of_smooth_of_hprin exampleTwo exampleThree
    (n := 4) primeFactorsFour exampleNsS exampleNsS exampleNsT exampleNsR
    (by convert exampleTorFourS) (by convert exampleTorFourS) (by convert exampleTorFourT)
    (by convert exampleAdd) ?_
  intro x y h hm
  simpa only [Nat.cast_ofNat] using hprin h (by convert hm)

end Nonvacuity

end WeierstrassCurve.Affine
