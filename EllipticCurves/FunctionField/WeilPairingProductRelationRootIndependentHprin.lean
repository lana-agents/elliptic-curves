/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairingProductRelationHprin
import EllipticCurves.FunctionField.WeilPairingProductRelationRootIndependent

/-!
# Antisymmetry for supplied roots over an ARBITRARY field, with `hprin` the only gate (rung 6)

`EllipticCurves.FunctionField.WeilPairingProductRelationRootIndependent` (`#868`) states
antisymmetry

```
e_n(S, g_T) · e_n(T, g_S) = 1,      e_n(S, g_T) = (e_n(T, g_S))⁻¹
```

for roots `g_S`, `g_T` the **caller** supplies, rather than roots the theorem produces — the form a
consumer holding a root from elsewhere can actually apply.  It does so over an algebraically closed
field.  **This file removes that `[IsAlgClosed F]` from all eight of its headlines**, at the cost of
the single hypothesis `hprin` and of nothing else.

## Where the instance came from, which is the only question that mattered

⚠️ `#907`'s delivery note predicted this file would need *"a different substitution with a different
justification"*, on the grounds that `#868` reaches a caller's root through
`weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq` rather than through the alternating property.
**The route claim is right and the conclusion drawn from it was wrong.**  That lemma carries no
`[IsAlgClosed F]` and no torsion hypothesis — `#868`'s docstring says so — so it was never the gate.
The instance enters `#868` in exactly one way: its headlines call `#845`'s
`exists_weilPairingElt_mul_swap_eq_one_{two,three}`, which `#907` has since generalised.

The lesson, recorded here because a reader of this file is the person who will next need it:
**ask where the instance is *introduced*, not how the theorem is *proved*.**  `grep -n IsAlgClosed`
plus a glance at which declarations sit below each `variable [IsAlgClosed F]` line answers it in a
minute; reasoning about proof routes answered it wrongly.

⚠️ **Nothing about curves is proved here.**  Each body is its `#868` twin's, transcribed, with one
call swapped — `exists_weilPairingElt_mul_swap_eq_one_{two,three}` becomes
`…_of_hprin_{two,three}` with `hprin` threaded through.  A reader should check this file by putting
the two side by side; the normalised diff is the intended review.

## ⚠️ On the name shape, which deliberately does not match `#907`

`#868` suffixes as `…_two_of_isAlgClosed` — the `_two` **before** the qualifier — while `#907`
writes `…_of_hprin_two`, with it after.  The names below follow **`#868`**, giving
`…_two_of_hprin`, because they sit beside `#868`'s and a reader comparing the two families wants the
shapes to line up.  Both spellings are consistent with the `## Naming` section of
`EllipticCurves.FunctionField.WeilPairing`, which constrains what `_two`/`_three` *mean* and not
where they sit.

## The `hprin` hypothesis

Quantified over the `n`-torsion points, exactly as in
`EllipticCurves.FunctionField.WeilPairingProductRelationHprin` and for the same reason: it is the
signature of the only dischargers that exist, `exists_nsmul_divisor_eq_divisor_mulByTwoEndo` and
`exists_nsmul_divisor_eq_divisor_mulByThreeEndo`.  The `AlgClosedRecovery` block below exhibits that
discharge, so the shape is checked rather than asserted.

## Main statements

At `n = 2` and `n = 3`, in the function field and in `μ_n(F)`:

* `WeierstrassCurve.Affine.weilPairingElt_mul_swap_eq_one_{two,three}_of_hprin`;
* `WeierstrassCurve.Affine.weilPairingElt_eq_inv_{two,three}_of_hprin`;
* `WeierstrassCurve.Affine.weilPairingMu_mul_swap_eq_one_{two,three}_of_hprin` and
  `WeierstrassCurve.Affine.weilPairingMu_eq_inv_{two,three}_of_hprin`, where the inverse is the
  **group** inverse of `rootsOfUnity n F`.

⚠️ In the `μ_n(F)` statements the index `n` is the index of the **value group** and is not tied to
the torsion of `S` and `T`; the two `hpow` data are hypotheses because `weilPairingMu` is indexed by
the *proof*.  That is `#868`'s arrangement, unchanged.

On placement: everything is in `WeierstrassCurve.Affine`, with `open CoordinateRing` rather than a
nested `namespace`.  ⚠️ `#903`: only `#print axioms` on the **fully qualified** name checks that.

## ⚠️ Why there is no `ℚ` non-vacuity block here, which is a judgement and not an omission

Every other file on this front ends with a certificate over a concrete curve.  This one does not,
deliberately.

`#868`'s certificates *produce* their roots, from `exists_gS_{two,three}_of_isAlgClosed` — a route
that exists only over `F̄`, so it cannot be copied here.  What is left to certify over `ℚ` is the
**point-side** configuration: three pairwise-distinct rational `n`-torsion points with `S ⊕ T = R`.
⚠️ `EllipticCurves.FunctionField.WeilPairingProductRelationHprin` (`#907`) already certifies exactly
that, on `y² = x³ − x` at `(0, 0)`, `(1, 0)`, `(−1, 0)`, and this file **imports** it.  A block here
would use the same curve and the same three points while *additionally* assuming `f_S`, `f_T`,
`g_S`, `g_T` and their divisor and rung-5 certificates — so it would demonstrate strictly **less**
than the one next door about the same configuration, and would read as evidence while supplying
none.

A certificate is worth writing when it shows some hypothesis is satisfiable that a reader might
doubt.  Here every such hypothesis is either already certified one import away or is one the merged
`F̄` twin assumes too.  **Recorded rather than silently skipped, because "this file has no
non-vacuity block" is otherwise indistinguishable from an oversight.**

Out of scope: discharging `hprin`, which is existence-shaped and never descends (`#899`'s test — is
the obstruction used to prove an equality, or to produce a witness?); any edit to `#845`'s, `#855`'s
or `#868`'s statements, none of which are deprecated, their consumers already carrying
`[IsAlgClosed F]`; non-degeneracy; Ward; rung 4.
-/

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

section Two

open Classical in
/-- **Antisymmetry at `n = 2` for roots the caller supplies, over an arbitrary field**, with `hprin`
the only gate:

```
e_2(S, g_T) · e_2(T, g_S) = 1.
```

`weilPairingElt_mul_swap_eq_one_two_of_isAlgClosed` (`WeilPairingProductRelationRootIndependent`) is
this statement with `[IsAlgClosed F]` in place of `hprin`; the conclusion is identical and no
hypothesis is added.

⚠️ `R = S ⊕ T` is not assumed `2`-torsion; the theorem this consumes derives it from `hadd`.  The
proof obtains that theorem's own pair of roots and rewrites each into the caller's by
`weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq` — the two `f`s at each point have the same divisor
because both are pinned to `2 (S)`, respectively `2 (T)`, by hypothesis. -/
theorem weilPairingElt_mul_swap_eq_one_two_of_hprin (h2 : (2 : F) ≠ 0)
    {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 2) (hmT : Point.some xT yT hT ∈ W.torsion 2)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion 2 →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f))
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
    hswap⟩ := exists_weilPairingElt_mul_swap_eq_one_of_hprin_two h2 hS hT hR hmS hmT hadd hprin
  rw [weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq hS.left (mulByTwoEndo h2)
        (mulByTwoEndo_algebraMap_base h2) two_ne_zero hfT hfT' (hdT.trans hdT'.symm) hgT hgT'
        huT huT',
      weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq hT.left (mulByTwoEndo h2)
        (mulByTwoEndo_algebraMap_base h2) two_ne_zero hfS hfS' (hdS.trans hdS'.symm) hgS hgS'
        huS huS']
  exact hswap

open Classical in
/-- **Antisymmetry at `n = 2` for supplied roots, in the quotable inverse form**
`e_2(S, g_T) = (e_2(T, g_S))⁻¹`, over an arbitrary field with `hprin` the only gate.  One line off
the product form. -/
theorem weilPairingElt_eq_inv_two_of_hprin (h2 : (2 : F) ≠ 0) {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 2) (hmT : Point.some xT yT hT ∈ W.torsion 2)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion 2 →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f))
    {fS fT gS gT : W.FunctionField} (hfS : fS ≠ 0) (hfT : fT ≠ 0)
    (hdS : divisor W fS = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ))
    (hdT : divisor W fT = Finsupp.single (pointClosedPoint hT.left) (2 : ℤ))
    (hgS : gS ≠ 0) (hgT : gT ≠ 0)
    (huS : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 fS)
    (huT : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 2 = mulByTwoEndo h2 fT) :
    weilPairingElt hS.left gT = (weilPairingElt hT.left gS)⁻¹ :=
  eq_inv_of_mul_eq_one_left (weilPairingElt_mul_swap_eq_one_two_of_hprin h2 hS hT hR hmS hmT
    hadd hprin hfS hfT hdS hdT hgS hgT huS huT)

open Classical in
/-- **Antisymmetry at `n = 2` for supplied roots, in `μ_n(F)`, over an arbitrary field** with
`hprin` the only gate.

⚠️ `n` is the index of the value group and is **not** tied to the `2`-torsion of `S` and `T`; the
two `hpow` data are hypotheses because `weilPairingMu` is indexed by the *proof*, and a caller
holding roots from elsewhere holds them.  At a `2`-torsion `T` they are
`weilPairingElt_pow_eq_one_of_gS_two_torsion` applied to the caller's own certificates.

The descent is `weilPairingMu_mul_swap_eq_one_of_weilPairingElt`, which needs no hypothesis beyond
the two `hpow` data and the `F(W)`-level relation — in particular it does not re-enter `hprin`. -/
theorem weilPairingMu_mul_swap_eq_one_two_of_hprin (h2 : (2 : F) ≠ 0)
    {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 2) (hmT : Point.some xT yT hT ∈ W.torsion 2)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion 2 →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f))
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
    (weilPairingElt_mul_swap_eq_one_two_of_hprin h2 hS hT hR hmS hmT hadd hprin hfS hfT hdS hdT
      hgS hgT huS huT)

open Classical in
/-- **Antisymmetry at `n = 2` for supplied roots, in `μ_n(F)`, in the quotable inverse form**, over
an arbitrary field with `hprin` the only gate.  The inverse is the **group** inverse of
`rootsOfUnity n F`, not a transport of the field division of `F(W)`. -/
theorem weilPairingMu_eq_inv_two_of_hprin (h2 : (2 : F) ≠ 0) {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 2) (hmT : Point.some xT yT hT ∈ W.torsion 2)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion 2 →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f))
    {fS fT gS gT : W.FunctionField} (hfS : fS ≠ 0) (hfT : fT ≠ 0)
    (hdS : divisor W fS = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ))
    (hdT : divisor W fT = Finsupp.single (pointClosedPoint hT.left) (2 : ℤ))
    (hgS : gS ≠ 0) (hgT : gT ≠ 0)
    (huS : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 fS)
    (huT : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 2 = mulByTwoEndo h2 fT)
    {n : ℕ} [NeZero n] (hpowST : weilPairingElt hS.left gT ^ n = 1)
    (hpowTS : weilPairingElt hT.left gS ^ n = 1) :
    weilPairingMu hS.left hpowST = (weilPairingMu hT.left hpowTS)⁻¹ :=
  eq_inv_of_mul_eq_one_left (weilPairingMu_mul_swap_eq_one_two_of_hprin h2 hS hT hR hmS hmT
    hadd hprin hfS hfT hdS hdT hgS hgT huS huT hpowST hpowTS)

end Two

section Three

open Classical in
/-- **Antisymmetry at `n = 3` for roots the caller supplies, over an arbitrary field**, with `hprin`
the only gate: the `n = 3` mirror of `weilPairingElt_mul_swap_eq_one_two_of_hprin`, and
`weilPairingElt_mul_swap_eq_one_three_of_isAlgClosed` with `hprin` in place of `[IsAlgClosed F]`.
Only the pullback differs from the `n = 2` twin, `mulByThreeEndo h2 h3` for `mulByTwoEndo h2`. -/
theorem weilPairingElt_mul_swap_eq_one_three_of_hprin (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 3) (hmT : Point.some xT yT hT ∈ W.torsion 3)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion 3 →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f))
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
    hswap⟩ :=
      exists_weilPairingElt_mul_swap_eq_one_of_hprin_three h2 h3 hS hT hR hmS hmT hadd hprin
  rw [weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq hS.left (mulByThreeEndo h2 h3)
        (mulByThreeEndo_algebraMap_base h2 h3) three_ne_zero hfT hfT' (hdT.trans hdT'.symm) hgT
        hgT' huT huT',
      weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq hT.left (mulByThreeEndo h2 h3)
        (mulByThreeEndo_algebraMap_base h2 h3) three_ne_zero hfS hfS' (hdS.trans hdS'.symm) hgS
        hgS' huS huS']
  exact hswap

open Classical in
/-- **Antisymmetry at `n = 3` for supplied roots, in the quotable inverse form**
`e_3(S, g_T) = (e_3(T, g_S))⁻¹`, over an arbitrary field with `hprin` the only gate. -/
theorem weilPairingElt_eq_inv_three_of_hprin (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 3) (hmT : Point.some xT yT hT ∈ W.torsion 3)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion 3 →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f))
    {fS fT gS gT : W.FunctionField} (hfS : fS ≠ 0) (hfT : fT ≠ 0)
    (hdS : divisor W fS = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ))
    (hdT : divisor W fT = Finsupp.single (pointClosedPoint hT.left) (3 : ℤ))
    (hgS : gS ≠ 0) (hgT : gT ≠ 0)
    (huS : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 fS)
    (huT : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 3 = mulByThreeEndo h2 h3 fT) :
    weilPairingElt hS.left gT = (weilPairingElt hT.left gS)⁻¹ :=
  eq_inv_of_mul_eq_one_left (weilPairingElt_mul_swap_eq_one_three_of_hprin h2 h3 hS hT hR hmS hmT
    hadd hprin hfS hfT hdS hdT hgS hgT huS huT)

open Classical in
/-- **Antisymmetry at `n = 3` for supplied roots, in `μ_n(F)`, over an arbitrary field** with
`hprin` the only gate.  As at `n = 2`, `n` indexes the value group and the two `hpow` data are
hypotheses; at a `3`-torsion `T` they are `weilPairingElt_pow_eq_one_of_gS_three_baseField` applied
to the caller's own certificates. -/
theorem weilPairingMu_mul_swap_eq_one_three_of_hprin (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 3) (hmT : Point.some xT yT hT ∈ W.torsion 3)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion 3 →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f))
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
    (weilPairingElt_mul_swap_eq_one_three_of_hprin h2 h3 hS hT hR hmS hmT hadd hprin hfS hfT hdS
      hdT hgS hgT huS huT)

open Classical in
/-- **Antisymmetry at `n = 3` for supplied roots, in `μ_n(F)`, in the quotable inverse form**, over
an arbitrary field with `hprin` the only gate. -/
theorem weilPairingMu_eq_inv_three_of_hprin (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 3) (hmT : Point.some xT yT hT ∈ W.torsion 3)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion 3 →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f))
    {fS fT gS gT : W.FunctionField} (hfS : fS ≠ 0) (hfT : fT ≠ 0)
    (hdS : divisor W fS = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ))
    (hdT : divisor W fT = Finsupp.single (pointClosedPoint hT.left) (3 : ℤ))
    (hgS : gS ≠ 0) (hgT : gT ≠ 0)
    (huS : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 fS)
    (huT : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 3 = mulByThreeEndo h2 h3 fT)
    {n : ℕ} [NeZero n] (hpowST : weilPairingElt hS.left gT ^ n = 1)
    (hpowTS : weilPairingElt hT.left gS ^ n = 1) :
    weilPairingMu hS.left hpowST = (weilPairingMu hT.left hpowTS)⁻¹ :=
  eq_inv_of_mul_eq_one_left (weilPairingMu_mul_swap_eq_one_three_of_hprin h2 h3 hS hT hR hmS hmT
    hadd hprin hfS hfT hdS hdT hgS hgT huS huT hpowST hpowTS)

end Three

/-! ### Recovery of the merged `F̄` headlines

⚠️ These two blocks are the check that the quantified `hprin` is the **right shape**: a hypothesis
that nothing can discharge looks exactly like these statements from the outside.  Over an
algebraically closed field it is discharged by a single term, and what comes out is
`weilPairingElt_mul_swap_eq_one_{two,three}_of_isAlgClosed`'s conclusion on the nose.

`#907` made this block standard for `_of_hprin`-style weakenings on this front; it is four lines and
it is the difference between a theorem and a plausible-looking vacuity. -/

section AlgClosedRecovery

variable [IsAlgClosed F]

open Classical in
/-- Over `F̄`, `hprin` is `exists_nsmul_divisor_eq_divisor_mulByTwoEndo` and nothing else, so the
`n = 2` headline recovers `weilPairingElt_mul_swap_eq_one_two_of_isAlgClosed`. -/
example (h2 : (2 : F) ≠ 0) {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 2) (hmT : Point.some xT yT hT ∈ W.torsion 2)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    {fS fT gS gT : W.FunctionField} (hfS : fS ≠ 0) (hfT : fT ≠ 0)
    (hdS : divisor W fS = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ))
    (hdT : divisor W fT = Finsupp.single (pointClosedPoint hT.left) (2 : ℤ))
    (hgS : gS ≠ 0) (hgT : gT ≠ 0)
    (huS : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 fS)
    (huT : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 2 = mulByTwoEndo h2 fT) :
    weilPairingElt hS.left gT * weilPairingElt hT.left gS = 1 :=
  weilPairingElt_mul_swap_eq_one_two_of_hprin h2 hS hT hR hmS hmT hadd
    (fun h hm _ hf hd => exists_nsmul_divisor_eq_divisor_mulByTwoEndo h2 h hm hf hd)
    hfS hfT hdS hdT hgS hgT huS huT

open Classical in
/-- The `n = 3` mirror, recovering `weilPairingElt_mul_swap_eq_one_three_of_isAlgClosed` from
`exists_nsmul_divisor_eq_divisor_mulByThreeEndo`. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 3) (hmT : Point.some xT yT hT ∈ W.torsion 3)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    {fS fT gS gT : W.FunctionField} (hfS : fS ≠ 0) (hfT : fT ≠ 0)
    (hdS : divisor W fS = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ))
    (hdT : divisor W fT = Finsupp.single (pointClosedPoint hT.left) (3 : ℤ))
    (hgS : gS ≠ 0) (hgT : gT ≠ 0)
    (huS : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 fS)
    (huT : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 3 = mulByThreeEndo h2 h3 fT) :
    weilPairingElt hS.left gT * weilPairingElt hT.left gS = 1 :=
  weilPairingElt_mul_swap_eq_one_three_of_hprin h2 h3 hS hT hR hmS hmT hadd
    (fun h hm _ hf hd => exists_nsmul_divisor_eq_divisor_mulByThreeEndo h2 h3 h hm hf hd)
    hfS hfT hdS hdT hgS hgT huS huT

end AlgClosedRecovery

end WeierstrassCurve.Affine
