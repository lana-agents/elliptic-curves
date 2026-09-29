/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairingProductRelationHprinN
import EllipticCurves.FunctionField.WeilPairingProductRelationRootIndependent

/-!
# Antisymmetry for SUPPLIED roots at a GENERAL index `n`, over an arbitrary field (rung 6)

`EllipticCurves.FunctionField.WeilPairingProductRelationRootIndependent` (`#854`) and its
`hprin`-gated twin `…RootIndependentHprin` (`#909`) state antisymmetry

```
e_n(S, g_T) · e_n(T, g_S) = 1,      e_n(S, g_T) = (e_n(T, g_S))⁻¹
```

for roots `g_S`, `g_T` the **caller** supplies rather than roots the theorem produces — the form a
consumer holding a root from elsewhere can actually apply.  Both do it at `n = 2` and at `n = 3`
only.  **This file states all four of those conclusions at a general index**, over an arbitrary
field with `hprin` and two halving points as the whole gate, and recovers the closed-field form
from them at the bottom.

It is the second half of what `WeilPairingProductRelationHprinN`'s *"What is not achieved"* section
leaves open; the first half, the `μ_n(F)` twins of that file's own existential headlines, is
`EllipticCurves.FunctionField.WeilPairingProductRelationHprinNMu`.

## ⚠️ Nothing about curves is proved here, and the transfer was already index-free

`weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq` (`#854`) — the lemma that rewrites the theorem's
own root into the caller's — is **generic in the pullback** `φ` and in the exponent `m`: it binds
`(φ : W.FunctionField →+* W.FunctionField)`, `hφc` saying `φ` fixes the base field, and
`{m : ℕ} (hm : m ≠ 0)`, and it carries neither `[IsAlgClosed F]` nor any torsion hypothesis.  So
`mulByNEndo n hn` with `mulByNEndo_algebraMap_base n hn` is as good an argument to it as
`mulByTwoEndo h2` was, and the exponent slot takes `hnz` where the `n = 2` twin passed
`two_ne_zero`.

Each body below is its `…RootIndependentHprin` twin's, transcribed, with
`exists_weilPairingElt_mul_swap_eq_one_of_hprin_two` replaced by
`exists_weilPairingElt_mul_swap_eq_one_of_hprin_n` and the two halving points threaded through.  A
reader should check this file by putting the two side by side; the normalised diff is the intended
review.

⚠️ **`#909`'s own delivery note recorded the general lesson this file is the second instance of:
ask where the gate is *introduced*, not how the theorem is *proved*.**  The route through
`weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq` is not where the index `2` or `3` entered
`#854`/`#909`; it entered through the single call to the existential headline, which `#2266` has
since generalised.  `grep -n 'mulByTwoEndo\|mulByThreeEndo'` on the twin answers it in a minute.

## ⚠️ On the name shape, which follows `#854` and not `#2266`

`#854` and `#909` suffix as `…_two_of_isAlgClosed` and `…_two_of_hprin` — the index **before** the
qualifier — while `WeilPairingProductRelationHprinN` writes `…_of_hprin_n`, with it after.  The
names below follow **`#854`**, giving `…_n_of_hprin`, because they sit beside `#909`'s and a reader
comparing the two families wants the shapes to line up.  ⚠️ **So `…_n_of_hprin` here and
`…_of_hprin_n` one import away are two families and not a typo**; both spellings are consistent
with the `## Naming` section of `EllipticCurves.FunctionField.WeilPairing`, which constrains what
an index suffix *means* and not where it sits.

## ⚠️ Two indices, and in the `μ` statements they are genuinely independent

The isogeny index is `n`: it is the torsion of `S` and `T`, the exponent of the two rung-5
certificates, and the index of `mulByNEndo`.  ⚠️ **The index of the value group in the two
`weilPairingMu` headlines is a separate `m` with `[NeZero m]`, and it is not tied to `n`.**  That is
`#854`'s arrangement and it is forced by the shape of this family rather than chosen: the caller
supplies the two `hpow` data, so nothing here produces them and nothing here needs them at the
pullback's index.  ⚠️ **Contrast `WeilPairingProductRelationHprinNMu`, where the two indices
coincide** — an envelope that *produces* its `hpow` witnesses can only produce them at the index it
pulled back along, which is `#861`'s arrangement for the existential family.  At an `n`-torsion `T`
the caller's data at `m = n` is `weilPairingElt_pow_eq_one_of_gS_n_torsion` applied to the caller's
own certificates.

## The `hprin` hypothesis and the halving points

`hprin` is quantified over the `n`-torsion points, exactly as in
`EllipticCurves.FunctionField.WeilPairingProductRelationHprinN` and for the same reason: it is the
signature of the only discharger that exists at a general index,
`exists_nsmul_divisor_eq_divisor_mulByNEndo`.  The two halving points `n • P_S = S` and
`n • P_T = T` are what the general-`n` alternating property needs and are invisible in the numeral
twins, where `WeilPairingAlternatingBaseChange` supplies them inside the alternating input.  ⚠️
**A halving point for `R` is not a hypothesis**: `R = S ⊕ T`, so `P_S + P_T` halves it, and the
headline this file consumes derives that, along with `R`'s `n`-torsion.

The `AlgClosedRecovery` block below discharges both gates, so the shape is checked rather than
asserted.

## Main statements

At every `n ≠ 0` with `x([n]𝒫)` transcendental, in the function field and in `μ_m(F)`:

* `WeierstrassCurve.Affine.weilPairingElt_mul_swap_eq_one_n_of_hprin`;
* `WeierstrassCurve.Affine.weilPairingElt_eq_inv_n_of_hprin`;
* `WeierstrassCurve.Affine.weilPairingMu_mul_swap_eq_one_n_of_hprin` and
  `WeierstrassCurve.Affine.weilPairingMu_eq_inv_n_of_hprin`, where the inverse is the **group**
  inverse of `rootsOfUnity m F`.

On placement: everything is in `WeierstrassCurve.Affine`, with `open CoordinateRing` rather than a
nested `namespace`.  ⚠️ `#903`: only `#print axioms` on the **fully qualified** name checks that.

## ⚠️ Why there is no `ℚ` non-vacuity block here, which is a judgement and not an omission

`#909` declined one, with its reasoning recorded, and the same reasoning applies unchanged at a
general index; it is repeated rather than cited alone because *"this file has no non-vacuity
block"* is otherwise indistinguishable from an oversight.

`#854`'s certificates *produce* their roots, from `exists_gS_{two,three}_of_isAlgClosed`, so they
cannot be copied into a statement whose roots are hypotheses.  What is left to certify is the
**point-side** configuration: three pairwise-distinct `n`-torsion points with `S ⊕ T = R` and
halving points for two of them.  ⚠️ `EllipticCurves.FunctionField.WeilPairingProductRelationHprinN`
already certifies exactly that at `n = 2`, on `y² = x³ − x` over `AlgebraicClosure ℚ` at `(0, 0)`,
`(1, 0)`, `(−1, 0)`, and **this file imports it**.  A block here would use the same curve and the
same three points while *additionally* assuming `f_S`, `f_T`, `g_S`, `g_T` and their divisor and
rung-5 certificates — so it would demonstrate strictly **less** than the one next door about the
same configuration, and would read as evidence while supplying none.

⚠️ **And the route that would make it non-trivial collapses into that file's certificate.**  Over
`F̄` the roots *can* be produced, by `exists_gS_n`, and fed back in; but then the certificate's
statement has to quantify them existentially again, which is
`exists_weilPairingElt_mul_swap_eq_one_n_of_isAlgClosed` — the headline already certified one
import away.  That is why the block below is a **gate-discharge** certificate and not a curve one.

Out of scope: discharging `hprin` over a general field, which is existence-shaped and never
descends (`#899`'s test — is the obstruction used to prove an equality, or to produce a witness?);
any edit to `#845`'s, `#854`'s, `#909`'s or `#2266`'s statements, none of which are deprecated;
non-degeneracy; Ward; rung 4.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.1(b).
-/

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

open Classical in
/-- **Antisymmetry at every `n ≠ 0` for roots the caller supplies, over an arbitrary field**, with
`hprin` and two halving points as the whole gate:

```
e_n(S, g_T) · e_n(T, g_S) = 1.
```

`weilPairingElt_mul_swap_eq_one_two_of_hprin`
(`WeilPairingProductRelationRootIndependentHprin`) is this statement at `n = 2` with `(2 : F) ≠ 0`
in place of the transcendence datum and with its halving points supplied inside the alternating
input; the conclusion is identical and no hypothesis is added beyond the index.

⚠️ `R = S ⊕ T` is assumed neither `n`-torsion nor halvable; the theorem this consumes derives both
from `hadd`.  The proof obtains that theorem's own pair of roots and rewrites each into the
caller's by `weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq` — the two `f`s at each point have the
same divisor because both are pinned to `n (S)`, respectively `n (T)`, by hypothesis. -/
theorem weilPairingElt_mul_swap_eq_one_n_of_hprin {n : ℕ} (hnz : n ≠ 0)
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
          n • divisor W g₀ = divisor W (mulByNEndo n hn f))
    {fS fT gS gT : W.FunctionField} (hfS : fS ≠ 0) (hfT : fT ≠ 0)
    (hdS : divisor W fS = Finsupp.single (pointClosedPoint hS.left) (n : ℤ))
    (hdT : divisor W fT = Finsupp.single (pointClosedPoint hT.left) (n : ℤ))
    (hgS : gS ≠ 0) (hgT : gT ≠ 0)
    (huS : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n = mulByNEndo n hn fS)
    (huT : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ n = mulByNEndo n hn fT) :
    weilPairingElt hS.left gT * weilPairingElt hT.left gS = 1 := by
  obtain ⟨uS, huS⟩ := huS
  obtain ⟨uT, huT⟩ := huT
  obtain ⟨gS', gT', hgS', hgT', ⟨fS', hfS', hdS', uS', huS'⟩, ⟨fT', hfT', hdT', uT', huT'⟩,
    hswap⟩ := exists_weilPairingElt_mul_swap_eq_one_of_hprin_n hnz hn hS hT hR hmS hmT hadd
      hPS hPT hprin
  rw [weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq hS.left (mulByNEndo n hn)
        (mulByNEndo_algebraMap_base n hn) hnz hfT hfT' (hdT.trans hdT'.symm) hgT hgT' huT huT',
      weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq hT.left (mulByNEndo n hn)
        (mulByNEndo_algebraMap_base n hn) hnz hfS hfS' (hdS.trans hdS'.symm) hgS hgS' huS huS']
  exact hswap

open Classical in
/-- **Antisymmetry at every `n ≠ 0` for supplied roots, in the quotable inverse form**
`e_n(S, g_T) = (e_n(T, g_S))⁻¹`, over an arbitrary field, with `hprin` and two halving points as
the whole gate.  One line off the product form. -/
theorem weilPairingElt_eq_inv_n_of_hprin {n : ℕ} (hnz : n ≠ 0)
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
          n • divisor W g₀ = divisor W (mulByNEndo n hn f))
    {fS fT gS gT : W.FunctionField} (hfS : fS ≠ 0) (hfT : fT ≠ 0)
    (hdS : divisor W fS = Finsupp.single (pointClosedPoint hS.left) (n : ℤ))
    (hdT : divisor W fT = Finsupp.single (pointClosedPoint hT.left) (n : ℤ))
    (hgS : gS ≠ 0) (hgT : gT ≠ 0)
    (huS : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n = mulByNEndo n hn fS)
    (huT : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ n = mulByNEndo n hn fT) :
    weilPairingElt hS.left gT = (weilPairingElt hT.left gS)⁻¹ :=
  eq_inv_of_mul_eq_one_left (weilPairingElt_mul_swap_eq_one_n_of_hprin hnz hn hS hT hR hmS hmT
    hadd hPS hPT hprin hfS hfT hdS hdT hgS hgT huS huT)

open Classical in
/-- **Antisymmetry at every `n ≠ 0` for supplied roots, in `μ_m(F)`, over an arbitrary field**,
with `hprin` and two halving points as the whole gate.

⚠️ `m` is the index of the **value group** and is **not** tied to the `n`-torsion of `S` and `T`;
the two `hpow` data are hypotheses because `weilPairingMu` is indexed by the *proof*, and a caller
holding roots from elsewhere holds them.  At an `n`-torsion `T` and `m = n` they are
`weilPairingElt_pow_eq_one_of_gS_n_torsion` applied to the caller's own certificates.

The descent is `weilPairingMu_mul_swap_eq_one_of_weilPairingElt`, which needs no hypothesis beyond
the two `hpow` data and the `F(W)`-level relation — in particular it does not re-enter `hprin`, the
halving points or the pullback's index. -/
theorem weilPairingMu_mul_swap_eq_one_n_of_hprin {n : ℕ} (hnz : n ≠ 0)
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
          n • divisor W g₀ = divisor W (mulByNEndo n hn f))
    {fS fT gS gT : W.FunctionField} (hfS : fS ≠ 0) (hfT : fT ≠ 0)
    (hdS : divisor W fS = Finsupp.single (pointClosedPoint hS.left) (n : ℤ))
    (hdT : divisor W fT = Finsupp.single (pointClosedPoint hT.left) (n : ℤ))
    (hgS : gS ≠ 0) (hgT : gT ≠ 0)
    (huS : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n = mulByNEndo n hn fS)
    (huT : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ n = mulByNEndo n hn fT)
    {m : ℕ} [NeZero m] (hpowST : weilPairingElt hS.left gT ^ m = 1)
    (hpowTS : weilPairingElt hT.left gS ^ m = 1) :
    weilPairingMu hS.left hpowST * weilPairingMu hT.left hpowTS = 1 :=
  weilPairingMu_mul_swap_eq_one_of_weilPairingElt hS.left hT.left hpowST hpowTS
    (weilPairingElt_mul_swap_eq_one_n_of_hprin hnz hn hS hT hR hmS hmT hadd hPS hPT hprin
      hfS hfT hdS hdT hgS hgT huS huT)

open Classical in
/-- **Antisymmetry at every `n ≠ 0` for supplied roots, in `μ_m(F)`, in the quotable inverse
form**, over an arbitrary field, with `hprin` and two halving points as the whole gate.  ⚠️ The
inverse is the **group** inverse of `rootsOfUnity m F`, not a transport of the field division of
`F(W)`. -/
theorem weilPairingMu_eq_inv_n_of_hprin {n : ℕ} (hnz : n ≠ 0)
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
          n • divisor W g₀ = divisor W (mulByNEndo n hn f))
    {fS fT gS gT : W.FunctionField} (hfS : fS ≠ 0) (hfT : fT ≠ 0)
    (hdS : divisor W fS = Finsupp.single (pointClosedPoint hS.left) (n : ℤ))
    (hdT : divisor W fT = Finsupp.single (pointClosedPoint hT.left) (n : ℤ))
    (hgS : gS ≠ 0) (hgT : gT ≠ 0)
    (huS : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n = mulByNEndo n hn fS)
    (huT : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ n = mulByNEndo n hn fT)
    {m : ℕ} [NeZero m] (hpowST : weilPairingElt hS.left gT ^ m = 1)
    (hpowTS : weilPairingElt hT.left gS ^ m = 1) :
    weilPairingMu hS.left hpowST = (weilPairingMu hT.left hpowTS)⁻¹ :=
  eq_inv_of_mul_eq_one_left (weilPairingMu_mul_swap_eq_one_n_of_hprin hnz hn hS hT hR hmS hmT
    hadd hPS hPT hprin hfS hfT hdS hdT hgS hgT huS huT hpowST hpowTS)

/-! ### Both gates discharged over `F̄`

⚠️ This block is the file's **non-vacuity**, and it certifies a *discharge* rather than a curve:
that `hprin` and the two halving points are simultaneously satisfiable at a general index, and by
what.  Neither discharge is proved here; both are the ones
`EllipticCurves.FunctionField.WeilPairingProductRelationHprinN` cites —
`exists_nsmul_divisor_eq_divisor_mulByNEndo` and `nsmul_surjective_of_two_ne_zero` — and the
statements below are the closed-field root-independent headlines that
`WeilPairingProductRelationRootIndependent` has at `n = 2` and `n = 3` only.

⚠️ They are `example`s and not theorems **on purpose**: naming them would create a
`…_of_isAlgClosed` row in a family whose closed-field half lives in `#854`, and nothing in the
tree consumes them yet.  Promote them if a consumer appears; the proof is already here.
-/

section AlgClosedRecovery

variable [IsAlgClosed F]

open Classical in
/-- Over `F̄`, both gates go: `hprin` is `exists_nsmul_divisor_eq_divisor_mulByNEndo` and the two
halving points are `nsmul_surjective_of_two_ne_zero`, so the general-`n` headline gives
`weilPairingElt_mul_swap_eq_one_two_of_isAlgClosed`'s conclusion for supplied roots at **every**
index with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`. -/
example (h2 : (2 : F) ≠ 0) {n : ℕ} (hnc : ((n : ℤ) : F) ≠ 0) {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion n) (hmT : Point.some xT yT hT ∈ W.torsion n)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    {fS fT gS gT : W.FunctionField} (hfS : fS ≠ 0) (hfT : fT ≠ 0)
    (hdS : divisor W fS = Finsupp.single (pointClosedPoint hS.left) (n : ℤ))
    (hdT : divisor W fT = Finsupp.single (pointClosedPoint hT.left) (n : ℤ))
    (hgS : gS ≠ 0) (hgT : gT ≠ 0)
    (huS : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n
      = mulByNEndo n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hnc) fS)
    (huT : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ n
      = mulByNEndo n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hnc) fT) :
    weilPairingElt hS.left gT * weilPairingElt hT.left gS = 1 := by
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hnc
  have hnz : n ≠ 0 := by rintro rfl; simp at hnF
  obtain ⟨PS, hPS⟩ := nsmul_surjective_of_two_ne_zero (W := W) h2 hnz (Point.some xS yS hS)
  obtain ⟨PT, hPT⟩ := nsmul_surjective_of_two_ne_zero (W := W) h2 hnz (Point.some xT yT hT)
  exact weilPairingElt_mul_swap_eq_one_n_of_hprin hnz
    (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hnc)
    hS hT hR hmS hmT hadd hPS hPT
    (fun h hmem f hf hfdiv =>
      exists_nsmul_divisor_eq_divisor_mulByNEndo h2 hnc
        (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hnc) h hmem hf hfdiv)
    hfS hfT hdS hdT hgS hgT huS huT

open Classical in
/-- The `μ_m(F)` mirror of the recovery above, by the same two discharges.  ⚠️ `m` is still free:
the caller's `hpow` data are hypotheses here as they are over a general field. -/
example (h2 : (2 : F) ≠ 0) {n : ℕ} (hnc : ((n : ℤ) : F) ≠ 0) {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion n) (hmT : Point.some xT yT hT ∈ W.torsion n)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    {fS fT gS gT : W.FunctionField} (hfS : fS ≠ 0) (hfT : fT ≠ 0)
    (hdS : divisor W fS = Finsupp.single (pointClosedPoint hS.left) (n : ℤ))
    (hdT : divisor W fT = Finsupp.single (pointClosedPoint hT.left) (n : ℤ))
    (hgS : gS ≠ 0) (hgT : gT ≠ 0)
    (huS : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n
      = mulByNEndo n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hnc) fS)
    (huT : ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ n
      = mulByNEndo n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hnc) fT)
    {m : ℕ} [NeZero m] (hpowST : weilPairingElt hS.left gT ^ m = 1)
    (hpowTS : weilPairingElt hT.left gS ^ m = 1) :
    weilPairingMu hS.left hpowST * weilPairingMu hT.left hpowTS = 1 := by
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hnc
  have hnz : n ≠ 0 := by rintro rfl; simp at hnF
  obtain ⟨PS, hPS⟩ := nsmul_surjective_of_two_ne_zero (W := W) h2 hnz (Point.some xS yS hS)
  obtain ⟨PT, hPT⟩ := nsmul_surjective_of_two_ne_zero (W := W) h2 hnz (Point.some xT yT hT)
  exact weilPairingMu_mul_swap_eq_one_n_of_hprin hnz
    (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hnc)
    hS hT hR hmS hmT hadd hPS hPT
    (fun h hmem f hf hfdiv =>
      exists_nsmul_divisor_eq_divisor_mulByNEndo h2 hnc
        (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hnc) h hmem hf hfdiv)
    hfS hfT hdS hdT hgS hgT huS huT hpowST hpowTS

end AlgClosedRecovery

end WeierstrassCurve.Affine
