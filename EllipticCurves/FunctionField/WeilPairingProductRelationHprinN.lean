/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import EllipticCurves.FunctionField.PullbackPrincipalityN
import EllipticCurves.FunctionField.WeilPairingAlternatingAssemblyN
import EllipticCurves.FunctionField.WeilPairingDivisorSlotBilinearHprinN
import EllipticCurves.FunctionField.WeilPairingProductRelationHprin

/-!
# Antisymmetry of the Weil pairing at a GENERAL index `n` (rung 6)

Silverman *AEC* III.8.1(b): the Weil pairing is antisymmetric,

```
e_n(S, T) · e_n(T, S) = 1,      e_n(S, T) = (e_n(T, S))⁻¹.
```

Every instantiation of that statement in this development was at `n = 2` or at `n = 3`
(`WeilPairingProductRelation`, `WeilPairingProductRelationMu`, `WeilPairingProductRelationHprin`,
`WeilPairingProductRelationRootIndependent{,Hprin}`).  **This file states it at a general index**,
in two layers: over an arbitrary field with `hprin` and two halving points as the whole gate, and
over an algebraically closed field with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` and no hypothesis
beyond the setting.

## ⚠️ No new mathematics is proved here, and the reason is worth stating

The antisymmetry *engine* `weilPairingElt_mul_swap_eq_one`
(`EllipticCurves.FunctionField.WeilPairingAntisymmetric`) is **already** stated at a general index —
it binds `{n : ℕ} (hn : n ≠ 0)` and consumes `hpow : e_n(T, g_S) ^ n = 1` — and has been since it
was written.  What was missing was not a theorem about curves but the *instantiation*: the three
rung-5 roots, the product relation and the three alternating values, all produced at a general `n`
rather than at `2` and `3`.  Each of those four inputs already existed at a general `n`:

* `exists_gS_n` (`NthRootOfPullbackN`) — the rung-5 root, `hprin`-gated;
* `exists_prod_eq_of_pullback` (`WeilPairingProductRelation`) — ⚠️ **already general in the
  isogeny**: it takes the pullback `φ` as an argument, and `mulByNEndo n hn` is that argument;
* `exists_weilPairingElt_self_eq_one_of_hprin_n` (`WeilPairingAlternatingAssemblyN`) — the
  alternating property at a point;
* `weilPairingElt_pow_eq_one_of_gS_n_torsion` (`WeilPairingTranslationSlotHprinN`) — the `hpow`
  datum, whose two indices are independent and are both fed `n` here.

So each headline below is `exists_weilPairingElt_mul_swap_eq_one_of_hprin_two`'s proof with the
numeral removed, in the same sense that
`exists_weilPairingElt_divisorSlot_add_n_of_hprin` is `…_two_of_hprin`'s.  A reader comparing this
file with `WeilPairingProductRelationHprin` should find the bodies line-for-line the same apart
from `mulByTwoEndo h2 ↦ mulByNEndo n hn`, `two_ne_zero ↦ hnz`, the alternating input, and the
halving points; that is the intended way to check it.

## ⚠️ The gate is heavier than the divisor-slot rung's, and it is heavier for a reason

`WeilPairingDivisorSlotBilinearHprinN` needs `hprin` and nothing else, because divisor-slot
bilinearity consumes **no** alternating property at any point.  Antisymmetry consumes it at
**three** points — `S`, `T` and `R = S ⊕ T` — and at a general index the alternating property is
itself gated on a halving point (`exists_weilPairingElt_self_eq_one_of_hprin_n` binds
`{P : W.Point} (hPT : n • P = T)`), which at `n = 2` and `n = 3` is supplied by
`WeilPairingAlternatingBaseChange` and is not visible in the numeral headlines.  ⚠️ **Do not read
the two rungs as equally gated**; `WeilPairingAntisymmetric`'s own `## Non-vacuity` already says
the bilinearity instantiation is the cheaper one.

⚠️ **Two halving points, not three.**  `R` is `S ⊕ T`, so `P_S + P_T` halves it:
`n • (P_S + P_T) = n • P_S + n • P_T = S ⊕ T = R`.  The third hypothesis a naive transcription would
bind is therefore *derived*, and this is the one place where the general-`n` statement is cheaper
than its own shape suggests.  ⚠️ `R`'s `n`-torsion is derived in the same way — `W.torsion n` is a
subgroup, so `hadd ▸ add_mem hmS hmT` gives it — exactly as at `n = 2` and `n = 3`.

## ⚠️ What is *not* achieved

**`hprin` is not discharged over an arbitrary field, and cannot be by anything here.**  `#899`'s
test decides it: an `[IsAlgClosed F]` use that proves an *equality* descends to a general field,
and one that produces a *witness* does not.  The alternating inputs are equalities in `F(W)`, so
they are gone; `hprin` is an existence statement, so it stays, and the two `_of_hprin_n` headlines
carry it.  ⚠️ **Over `F̄` it is discharged, and the two `_of_isAlgClosed` headlines below take that
discharge** — `exists_nsmul_divisor_eq_divisor_mulByNEndo`
(`EllipticCurves.FunctionField.PullbackPrincipalityN`) for `hprin` and
`nsmul_surjective_of_two_ne_zero` (`EllipticCurves.Torsion.TwoTorsionOrder`) for the two halving
points — **so the closed-field layer states the conclusion with no gate at all**.  Neither
discharge is proved here; both are cited.

**No `μ`-valued twin, and no root-independent form.**  `weilPairingMu` is indexed by the proof that
the value is a root of unity, so its headlines take `[NeZero n]` in place of `hnz` and must
*produce* their `hpow` witnesses; that is a separate module of the same shape as
`WeilPairingProductRelationMu` is to `WeilPairingProductRelation`.  The root-independent family
routes through `weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq` rather than through the alternating
property and is likewise a different substitution.

**Nothing about the merged numeral headlines.**  The sixteen `_two` and sixteen `_three`
instantiations are not deprecated, not restated and not recovered from these: they are built from
`mulByTwoEndo` / `mulByThreeEndo`, which are different constructions from `mulByNEndo`, and
`WeilPairingFunctionN`'s `### Recovery of the merged numeral layers, compiled` is what would relate
them.  `#1304`/`#1308`'s rule stands — at those two indices the merged ones are the right thing to
cite.

## Main statements

* `exists_weilPairingElt_mul_swap_eq_one_of_hprin_n` — `e_n(S, T) · e_n(T, S) = 1` at every
  `n ≠ 0`, over an arbitrary field, given `hprin` at the three points and halving points for `S`
  and `T`.
* `exists_weilPairingElt_eq_inv_of_hprin_n` — the quotable inverse form
  `e_n(S, T) = (e_n(T, S))⁻¹`, under the same hypotheses.
* `exists_weilPairingElt_mul_swap_eq_one_n_of_isAlgClosed` and
  `exists_weilPairingElt_eq_inv_n_of_isAlgClosed` — the same two conclusions over an algebraically
  closed field at every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`, with no hypothesis beyond
  the setting and a triple of affine points with `S ⊕ T = R`.

## Non-vacuity

The certificate is at the bottom of the file and is run against the **closed-field** headline,
which is the one with no gate; the two `hprin`-gated headlines are certified only through it, and
that is stated there rather than left to be inferred.  ⚠️ **The index is `n = 2` and `S ≠ T`**, so
the instance is a genuine instance of antisymmetry rather than a disguised instance of the
alternating property.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.1(b).
-/

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

open Classical in
/-- The rung-5 datum at an `n`-torsion point together with the alternating property for **that**
root, over an arbitrary field: the affine-divisor repackaging of
`exists_weilPairingElt_self_eq_one_of_hprin_n`, and the general-`n` twin of
`WeilPairingProductRelationHprin`'s private `rungFiveAltHprin_two`.

⚠️ `hprin` is taken here in its **point-local** form, unlike in the headlines below, and the
halving point `P` is the one the alternating property needs at a general index. -/
private lemma rungFiveAltHprin_n {n : ℕ} (hnz : n ≠ 0)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) {x y : F}
    (h : W.Nonsingular x y) (htors : Point.some x y h ∈ W.torsion n)
    {P : W.Point} (hP : n • P = Point.some x y h)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀ = divisor W (mulByNEndo n hn f)) :
    ∃ f g : W.FunctionField, f ≠ 0 ∧ g ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) ∧
      (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n = mulByNEndo n hn f) ∧
      weilPairingElt h.left g = 1 := by
  obtain ⟨f, hf, hdivproj, g, hg, hu, _, halt⟩ :=
    exists_weilPairingElt_self_eq_one_of_hprin_n hnz hn h htors hP hprin
  exact ⟨f, g, hf, hg, divisor_eq_single_of_divisorProj_eq_single_sub_single hdivproj, hu, halt⟩

open Classical in
/-- **Antisymmetry of the Weil pairing at every `n ≠ 0` over an arbitrary field**, with `hprin` and
two halving points as the whole gate:

```
e_n(S, T) · e_n(T, S) = 1.
```

`exists_weilPairingElt_mul_swap_eq_one_of_hprin_two` is this statement at `n = 2` with
`(2 : F) ≠ 0` in place of the transcendence datum and with its halving points supplied inside the
alternating input; the conclusion here is identical and the two roots are exposed the same way.

⚠️ `hprin` is quantified over the *point* because roots are needed at all three of `S`, `T` and
`R` — `WeilPairingDivisorSlotBilinearHprinN`'s shape, not a new one.  ⚠️ Neither `R`'s `n`-torsion
nor a halving point for `R` is a hypothesis: `W.torsion n` is a subgroup and `P_S + P_T` halves
`R`, so both are derived. -/
theorem exists_weilPairingElt_mul_swap_eq_one_of_hprin_n {n : ℕ} (hnz : n ≠ 0)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion n) (hmT : Point.some xT yT hT ∈ W.torsion n)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    {PS PT : W.Point} (hPS : n • PS = Point.some xS yS hS)
    (hPT : n • PT = Point.some xT yT hT)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion n →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          n • divisor W g₀ = divisor W (mulByNEndo n hn f)) :
    ∃ gS gT : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n = mulByNEndo n hn f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ n = mulByNEndo n hn f) ∧
      weilPairingElt hS.left gT * weilPairingElt hT.left gS = 1 := by
  have hmR : Point.some xR yR hR ∈ W.torsion n := hadd ▸ add_mem hmS hmT
  have hPR : n • (PS + PT) = Point.some xR yR hR := by
    rw [smul_add, hPS, hPT, hadd]
  obtain ⟨fS, gS, hfS, hgS, hdS, ⟨uS, huS⟩, haltS⟩ :=
    rungFiveAltHprin_n hnz hn hS hmS hPS (hprin hS hmS)
  obtain ⟨fT, gT, hfT, hgT, hdT, ⟨uT, huT⟩, haltT⟩ :=
    rungFiveAltHprin_n hnz hn hT hmT hPT (hprin hT hmT)
  obtain ⟨fR, gR, hfR, hgR, hdR, ⟨uR, huR⟩, haltR⟩ :=
    rungFiveAltHprin_n hnz hn hR hmR hPR (hprin hR hmR)
  obtain ⟨c, k, hc, hk, hprod⟩ :=
    exists_prod_eq_of_pullback (mulByNEndo n hn) (mulByNEndo_algebraMap_base n hn)
      hnz hS hT hR hadd hfS hfT hfR hdS hdT hdR hgS hgT hgR huS huT huR
  have hwR : weilPairingElt hR.left
      (algebraMap F W.FunctionField c * mulByNEndo n hn k) = 1 := by
    rw [weilPairingElt_mul, weilPairingElt_algebraMap hR.left hc,
      weilPairingElt_mulByNEndo_of_baseField hR.left n hn (mem_torsion_iff.mp hmR) hk, mul_one]
  refine ⟨gS, gT, hgS, hgT, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩, ?_⟩
  exact weilPairingElt_mul_swap_eq_one hS.left hT.left hR.left hadd hgS hgT hprod hwR hnz
    (weilPairingElt_pow_eq_one_of_gS_n_torsion hT.left n hn (mem_torsion_iff.mp hmT) hgS huS)
    haltS haltT haltR

open Classical in
/-- **Antisymmetry at every `n ≠ 0` in the quotable inverse form** `e_n(S, T) = (e_n(T, S))⁻¹`,
over an arbitrary field, with `hprin` and two halving points as the whole gate.  Immediate from the
previous theorem: `a * b = 1` already forces `a = b⁻¹` in a field, so no nonvanishing hypothesis is
added and the two roots are carried through unchanged. -/
theorem exists_weilPairingElt_eq_inv_of_hprin_n {n : ℕ} (hnz : n ≠ 0)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion n) (hmT : Point.some xT yT hT ∈ W.torsion n)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    {PS PT : W.Point} (hPS : n • PS = Point.some xS yS hS)
    (hPT : n • PT = Point.some xT yT hT)
    (hprin : ∀ {x y : F} (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion n →
      ∀ f : W.FunctionField, f ≠ 0 →
        divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
        ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
          n • divisor W g₀ = divisor W (mulByNEndo n hn f)) :
    ∃ gS gT : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n = mulByNEndo n hn f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ n = mulByNEndo n hn f) ∧
      weilPairingElt hS.left gT = (weilPairingElt hT.left gS)⁻¹ := by
  obtain ⟨gS, gT, hgS, hgT, hcS, hcT, hswap⟩ :=
    exists_weilPairingElt_mul_swap_eq_one_of_hprin_n hnz hn hS hT hR hmS hmT hadd hPS hPT hprin
  exact ⟨gS, gT, hgS, hgT, hcS, hcT, eq_inv_of_mul_eq_one_left hswap⟩

/-! ### The same two headlines over `F̄`, with no hypothesis beyond the setting -/

open Classical in
/-- **Antisymmetry of the Weil pairing at every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`,
over an algebraically closed field, with no hypothesis beyond the setting:**

```
e_n(S, T) · e_n(T, S) = 1.
```

The `hprin`-gated headline above with both of its gates discharged, and neither discharge is new
here: `hprin` is `exists_nsmul_divisor_eq_divisor_mulByNEndo`
(`EllipticCurves.FunctionField.PullbackPrincipalityN`) and the two halving points are
`nsmul_surjective_of_two_ne_zero` (`EllipticCurves.Torsion.TwoTorsionOrder`).  This is the
general-`n` form of `exists_weilPairingElt_mul_swap_eq_one_two` and
`exists_weilPairingElt_mul_swap_eq_one_three`.

⚠️ **`n ≠ 0` is not a hypothesis and must not be added**: `((n : ℤ) : F) ≠ 0` already implies it,
and the index condition is the sharper of the two.  ⚠️ The transcendence datum is
`transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`, which is the term
`exists_gS_of_ne_zero_of_isAlgClosed` writes, **so a caller holding either statement's rung-5
certificate can `rw` with the other**; picking the `_of_isAlgClosed` transcendence instead would
produce a syntactically different `mulByNEndo` and break that. -/
theorem exists_weilPairingElt_mul_swap_eq_one_n_of_isAlgClosed [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    {n : ℕ} (hnc : ((n : ℤ) : F) ≠ 0) {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion n) (hmT : Point.some xT yT hT ∈ W.torsion n)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR) :
    ∃ gS gT : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hnc) f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hnc) f) ∧
      weilPairingElt hS.left gT * weilPairingElt hT.left gS = 1 := by
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hnc
  have hnz : n ≠ 0 := by rintro rfl; simp at hnF
  obtain ⟨PS, hPS⟩ := nsmul_surjective_of_two_ne_zero (W := W) h2 hnz (Point.some xS yS hS)
  obtain ⟨PT, hPT⟩ := nsmul_surjective_of_two_ne_zero (W := W) h2 hnz (Point.some xT yT hT)
  exact exists_weilPairingElt_mul_swap_eq_one_of_hprin_n hnz
    (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hnc)
    hS hT hR hmS hmT hadd hPS hPT
    fun h hmem f hf hfdiv =>
      exists_nsmul_divisor_eq_divisor_mulByNEndo h2 hnc
        (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hnc) h hmem hf hfdiv

open Classical in
/-- **Antisymmetry in the quotable inverse form at every `n` with `(2 : F) ≠ 0` and
`((n : ℤ) : F) ≠ 0`, over an algebraically closed field**, with no hypothesis beyond the setting:
`e_n(S, T) = (e_n(T, S))⁻¹`.  Immediate from the previous theorem. -/
theorem exists_weilPairingElt_eq_inv_n_of_isAlgClosed [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    {n : ℕ} (hnc : ((n : ℤ) : F) ≠ 0) {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion n) (hmT : Point.some xT yT hT ∈ W.torsion n)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR) :
    ∃ gS gT : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hnc) f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hnc) f) ∧
      weilPairingElt hS.left gT = (weilPairingElt hT.left gS)⁻¹ := by
  obtain ⟨gS, gT, hgS, hgT, hcS, hcT, hswap⟩ :=
    exists_weilPairingElt_mul_swap_eq_one_n_of_isAlgClosed h2 hnc hS hT hR hmS hmT hadd
  exact ⟨gS, gT, hgS, hgT, hcS, hcT, eq_inv_of_mul_eq_one_left hswap⟩

/-! ### Non-vacuity

⚠️ The certificate is run against the **`F̄` headline**, because it is the one with no gate; the two
`hprin`-gated headlines above are certified only through it, and that is said in the module
docstring rather than papered over here.

The curve is the shared `EllipticCurves.Fixture.y2EqX3SubX` over
`EllipticCurves.Fixture.AlgClosedQ`, and the index is `n = 2` — ⚠️ **chosen because it is the
cheapest index here**, `(0, 0)`, `(1, 0)` and `(−1, 0)` being `2`-torsion outright,
with `(0, 0) ⊕ (1, 0) = (−1, 0)`.  `S ≠ T` there, so the instance is a genuine instance of
*antisymmetry* and not a disguised instance of the alternating property — the distinction
`WeilPairingProductRelation`'s own non-vacuity section draws, and the reason its `n = 3`
certificate is weaker than its `n = 2` one.

⚠️ **The certificate is at a numeral index and the theorem is at a general one, and that is not a
gap in it**: what a non-vacuity certificate has to show is that the hypotheses are simultaneously
satisfiable, and `n` is universally quantified in the statement, so one index does it.

⚠️ **Do not read the `2` as a ceiling.**  Higher indices are certified across this directory,
including in modules cited above as inputs, and `(0, 0)` is reachable at every *even* index by the
`4 = 2 * 2` / `mul_nsmul` step with which `WeilPairingDivisorSlotBilinearHprinN` lifts these same
three points to `torsion 4`.  The true statement is narrower and is a census at a clock, not an
impossibility: the antisymmetry family by itself certifies `2` and `3` and no other index, a set
this file does not move.  ⚠️ **Run the seed rather than trusting that sentence**, since the next
row added to the family falsifies it:

```
git grep -ohE '\.torsion [0-9]+' <ref> \
  -- 'EllipticCurves/FunctionField/WeilPairingProductRelation*.lean' | sort -u
```
-/

section Nonvacuity

open EllipticCurves.Fixture

private lemma exampleTwoAC : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleNsSAC : (y2EqX3SubX AlgClosedQ).Nonsingular 0 0 :=
  (y2EqX3SubX AlgClosedQ).equation_iff_nonsingular.mp (by
    norm_num [y2EqX3SubX, WeierstrassCurve.Affine.equation_iff])

private lemma exampleNsTAC : (y2EqX3SubX AlgClosedQ).Nonsingular 1 0 :=
  (y2EqX3SubX AlgClosedQ).equation_iff_nonsingular.mp (by
    norm_num [y2EqX3SubX, WeierstrassCurve.Affine.equation_iff])

private lemma exampleNsRAC : (y2EqX3SubX AlgClosedQ).Nonsingular (-1) 0 :=
  (y2EqX3SubX AlgClosedQ).equation_iff_nonsingular.mp (by
    norm_num [y2EqX3SubX, WeierstrassCurve.Affine.equation_iff])

open Classical in
private lemma exampleTorSAC :
    Point.some (0 : AlgClosedQ) 0 exampleNsSAC ∈ (y2EqX3SubX AlgClosedQ).torsion 2 :=
  (mem_torsion_two_some_iff exampleNsSAC).mpr (by norm_num [y2EqX3SubX])

open Classical in
private lemma exampleTorTAC :
    Point.some (1 : AlgClosedQ) 0 exampleNsTAC ∈ (y2EqX3SubX AlgClosedQ).torsion 2 :=
  (mem_torsion_two_some_iff exampleNsTAC).mpr (by norm_num [y2EqX3SubX])

private lemma exampleAddAC :
    Point.some (0 : AlgClosedQ) 0 exampleNsSAC + Point.some (1 : AlgClosedQ) 0 exampleNsTAC
      = Point.some (-1 : AlgClosedQ) 0 exampleNsRAC := by
  rw [Point.add_of_X_ne (by norm_num)]
  simp only [Point.some.injEq]
  norm_num [y2EqX3SubX, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.negY]

private lemma exampleIndexAC : (((2 : ℕ) : ℤ) : AlgClosedQ) ≠ 0 := by norm_num

open Classical in
/-- **The general-`n` antisymmetry headline, instantiated on a curve that exists**, at `n = 2` and
at two **distinct** named `2`-torsion points of `y² = x³ − x` over `AlgebraicClosure ℚ`. -/
example : ∃ gS gT : (y2EqX3SubX AlgClosedQ).FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
    (∃ f : (y2EqX3SubX AlgClosedQ).FunctionField, f ≠ 0 ∧
      (y2EqX3SubX AlgClosedQ).divisor f
        = Finsupp.single (pointClosedPoint exampleNsSAC.left) ((2 : ℕ) : ℤ) ∧
      ∃ u : (y2EqX3SubX AlgClosedQ).CoordinateRingˣ,
        (u : (y2EqX3SubX AlgClosedQ).CoordinateRing) • gS ^ (2 : ℕ)
          = mulByNEndo 2 (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero
              exampleTwoAC exampleIndexAC) f) ∧
    (∃ f : (y2EqX3SubX AlgClosedQ).FunctionField, f ≠ 0 ∧
      (y2EqX3SubX AlgClosedQ).divisor f
        = Finsupp.single (pointClosedPoint exampleNsTAC.left) ((2 : ℕ) : ℤ) ∧
      ∃ u : (y2EqX3SubX AlgClosedQ).CoordinateRingˣ,
        (u : (y2EqX3SubX AlgClosedQ).CoordinateRing) • gT ^ (2 : ℕ)
          = mulByNEndo 2 (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero
              exampleTwoAC exampleIndexAC) f) ∧
    weilPairingElt exampleNsSAC.left gT * weilPairingElt exampleNsTAC.left gS = 1 :=
  exists_weilPairingElt_mul_swap_eq_one_n_of_isAlgClosed exampleTwoAC exampleIndexAC
    exampleNsSAC exampleNsTAC exampleNsRAC exampleTorSAC exampleTorTAC exampleAddAC

end Nonvacuity

end WeierstrassCurve.Affine
