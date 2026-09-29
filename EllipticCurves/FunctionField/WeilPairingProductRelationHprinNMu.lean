/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairingProductRelationHprinN

/-!
# Antisymmetry of the Weil pairing in `μ_n(F)` at a GENERAL index `n` (rung 6)

Silverman *AEC* III.8.1(b) in the **value group**: for `S`, `T` in `E[n]`,

```
μ_n(S, T) · μ_n(T, S) = 1,      μ_n(S, T) = (μ_n(T, S))⁻¹      in rootsOfUnity n F.
```

`EllipticCurves.FunctionField.WeilPairingProductRelationHprinN` states the two `F(W)`-level forms
of this at a general index; **this file is its `μ_n(F)` twin**, standing to it as
`WeilPairingProductRelationMu` stands to `WeilPairingProductRelation` and as
`exists_weilPairingMu_{mul_swap_eq_one,eq_inv}_of_hprin_{two,three}`
(`WeilPairingProductRelationHprin`) stand to their `weilPairingElt` siblings at the two numerals.
Its own predecessor's *"What is not achieved"* section names it: *"No `μ`-valued twin … that is a
separate module of the same shape as `WeilPairingProductRelationMu` is to
`WeilPairingProductRelation`."*

## ⚠️ No new mathematics, and the descent is the one that was already general

The whole content is `weilPairingMu_mul_swap_eq_one_of_weilPairingElt`
(`EllipticCurves.FunctionField.WeilPairingAntisymmetricMu`), which was written at a general index
and takes **no** hypothesis beyond the two `hpow` data and the `F(W)`-level relation itself: it does
not re-enter `hprin`, the product relation, the alternating property or the divisor slot.  That is
the property its own docstring calls the reason it is stated before the theorem it generalises, and
it is what makes this file a transcription rather than an argument.

So each headline below is `exists_weilPairingMu_mul_swap_eq_one_of_hprin_two`'s proof with the
numeral removed, over the general-`n` `weilPairingElt` headline instead of the `n = 2` one.  A
reader comparing this file with `WeilPairingProductRelationHprin`'s `Two` section should find the
bodies line-for-line the same apart from `mulByTwoEndo h2 ↦ mulByNEndo n hn`,
`weilPairingElt_pow_eq_one_of_gS_two_torsion ↦ weilPairingElt_pow_eq_one_of_gS_n_torsion`, and the
two halving points the general-`n` alternating input needs; that is the intended way to check it.

## ⚠️ `[NeZero n]` in place of `n ≠ 0`, and the asymmetry is forced rather than chosen

`weilPairingMu` occurs in the **statement** of every headline below and needs `[NeZero n]` to
elaborate, so the index condition cannot be a hypothesis produced inside the proof.  `NeZero.ne n`
recovers the `hnz : n ≠ 0` that the `weilPairingElt` headlines bind, and is how each body feeds
them.  ⚠️ **In the two `_of_isAlgClosed` headlines `[NeZero n]` is therefore bound *alongside*
`((n : ℤ) : F) ≠ 0`, which already implies it** — the instance is carrying elaboration, not
strength, and `exists_weilPairingMu_divisorSlot_add_of_ne_zero_of_hprin`
(`WeilPairingDivisorSlotBilinearHprinN`) binds the same redundant pair for the same reason.  This
is the one place the `μ_n` layer's signature is *longer* than its `F(W)` sibling's rather than
shorter.

## ⚠️ The `hpow` data are produced, not assumed — and which torsion datum produces which

Both are existentially bound in the conclusion, because `weilPairingMu` is indexed by the *proof*
that the value is an `n`-th root of unity and two different proofs give two different terms.  They
come from `weilPairingElt_pow_eq_one_of_gS_n_torsion`
(`EllipticCurves.FunctionField.WeilPairingTranslationSlotHprinN`) applied to the rung-5
certificates the `weilPairingElt` envelope already carries, and ⚠️ **the indices cross**:
`hpowST : e(S, g_T) ^ n = 1` consumes the `n`-torsion of `S` and the certificate of `g_T`, and
`hpowTS` the other pair.  Getting that backwards does not typecheck, which is the only reason it is
safe to say so only here.

⚠️ The `μ_n` exponent is the *same* `n` as the isogeny in this file, unlike in
`weilPairingElt_pow_eq_one_of_gS_n_torsion`, where the two indices are genuinely independent, and
unlike in `WeilPairingProductRelationRootIndependentHprin`, where the caller supplies the `hpow`
data and the value group's index is free.  That is `#861`'s arrangement for the *existential*
family, unchanged: an envelope that produces its own witnesses can only produce them at the index
it pulled back along.

## ⚠️ What is *not* achieved

**`hprin` is not discharged over an arbitrary field**, and nothing here could do it: `#899`'s test
sends an existence-shaped obstruction to the general field unchanged.  The two `_of_hprin_n`
headlines carry it; over `F̄` it is discharged, by the same two citations
`WeilPairingProductRelationHprinN` uses and neither of them new here
(`exists_nsmul_divisor_eq_divisor_mulByNEndo` for `hprin`, `nsmul_surjective_of_two_ne_zero` for the
halving points).

**No root-independent `μ_n` form at general `n` from this file.**  A caller who already holds a root
cannot apply an existential envelope; the `∀ g` forms at both levels are
`EllipticCurves.FunctionField.WeilPairingProductRelationRootIndependentHprinN`, which imports this
file's `weilPairingElt` predecessor and not this file — the descent it instantiates is the same
`weilPairingMu_mul_swap_eq_one_of_weilPairingElt`, against a caller's roots rather than produced
ones.

**Nothing about the merged numeral headlines.**  The sixteen `_two` and sixteen `_three`
instantiations are not deprecated, not restated and not recovered from these: they are built from
`mulByTwoEndo` / `mulByThreeEndo`, which are different constructions from `mulByNEndo`.  `#1304`
and `#1308`'s rule stands — at those two indices the merged ones are the right thing to cite.

## Main statements

* `exists_weilPairingMu_mul_swap_eq_one_of_hprin_n` — `μ_n(S, T) · μ_n(T, S) = 1` at every `n`
  with `[NeZero n]`, over an arbitrary field, given `hprin` at the three points and halving points
  for `S` and `T`;
* `exists_weilPairingMu_eq_inv_of_hprin_n` — the quotable inverse form under the same hypotheses,
  where the inverse is the **group** inverse of `rootsOfUnity n F` and not a transport of the field
  division of `F(W)`;
* `exists_weilPairingMu_mul_swap_eq_one_n_of_isAlgClosed` and
  `exists_weilPairingMu_eq_inv_n_of_isAlgClosed` — the same two conclusions over an algebraically
  closed field with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`, with no hypothesis beyond the setting and
  a triple of affine points with `S ⊕ T = R`.

## Non-vacuity

The certificate at the bottom of the file is run against the **closed-field** headline, which is
the one with no gate; the two `hprin`-gated headlines are certified only through it, and that is
stated here rather than left to be inferred.  ⚠️ **The index is `n = 2` and `S ≠ T`**, so the
instance is a genuine instance of antisymmetry and not a disguised instance of the alternating
property, and the value group it lands in is `rootsOfUnity 2 (AlgebraicClosure ℚ)`, which is not
trivial.  ⚠️ **The certificate is at a numeral index and the theorem is at a general one, and that
is not a gap**: what it has to show is that the hypotheses are simultaneously satisfiable, and `n`
is universally quantified, so one index does it.  ⚠️ **Do not read the `2` as a ceiling** — the
statement is at every `n`, and the census of indices this *family* certifies is a census at a clock
that the next row added to it falsifies.  Run the seed rather than quoting a number:

```
git grep -ohE '\.torsion [0-9]+' <ref> \
  -- 'EllipticCurves/FunctionField/WeilPairingProductRelation*.lean' | sort -u
```

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.1(b).
-/

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

open Classical in
/-- **Antisymmetry of the Weil pairing in `μ_n(F)` at every `n` with `[NeZero n]`, over an
arbitrary field**, with `hprin` and two halving points as the whole gate:

```
μ_n(S, T) · μ_n(T, S) = 1      in rootsOfUnity n F.
```

`exists_weilPairingMu_mul_swap_eq_one_of_hprin_two` (`WeilPairingProductRelationHprin`) is this
statement at `n = 2` with `(2 : F) ≠ 0` in place of the transcendence datum and with its halving
points supplied inside the alternating input; the conclusion here is identical and the two roots
and the two `hpow` data are exposed the same way.

The envelope is `exists_weilPairingElt_mul_swap_eq_one_of_hprin_n`'s, extended by the two `hpow`
data, which are **produced** from the rung-5 certificates that envelope already carries and are
bound existentially because `weilPairingMu` is indexed by the proof.  ⚠️ Neither `R`'s `n`-torsion
nor a halving point for `R` is a hypothesis: `W.torsion n` is a subgroup and `P_S + P_T` halves
`R`, so the `weilPairingElt` headline derives both. -/
theorem exists_weilPairingMu_mul_swap_eq_one_of_hprin_n {n : ℕ} [NeZero n]
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
      ∃ hpowST : weilPairingElt hS.left gT ^ n = 1,
        ∃ hpowTS : weilPairingElt hT.left gS ^ n = 1,
          weilPairingMu hS.left hpowST * weilPairingMu hT.left hpowTS = 1 := by
  obtain ⟨gS, gT, hgS, hgT, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩, hswap⟩ :=
    exists_weilPairingElt_mul_swap_eq_one_of_hprin_n (NeZero.ne n) hn hS hT hR hmS hmT hadd
      hPS hPT hprin
  have hpowST : weilPairingElt hS.left gT ^ n = 1 :=
    weilPairingElt_pow_eq_one_of_gS_n_torsion hS.left n hn (mem_torsion_iff.mp hmS) hgT huT
  have hpowTS : weilPairingElt hT.left gS ^ n = 1 :=
    weilPairingElt_pow_eq_one_of_gS_n_torsion hT.left n hn (mem_torsion_iff.mp hmT) hgS huS
  exact ⟨gS, gT, hgS, hgT, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩, hpowST, hpowTS,
    weilPairingMu_mul_swap_eq_one_of_weilPairingElt hS.left hT.left hpowST hpowTS hswap⟩

open Classical in
/-- **Antisymmetry in `μ_n(F)` at every `n` with `[NeZero n]` in the quotable inverse form**
`μ_n(S, T) = (μ_n(T, S))⁻¹`, over an arbitrary field, with `hprin` and two halving points as the
whole gate.

⚠️ The inverse is the **group** inverse of `rootsOfUnity n F`, obtained by
`eq_inv_of_mul_eq_one_left` in that group — not a transport of the field division of `F(W)`, which
is what makes the `μ_n` form the one worth quoting.  One line off the product form; no nonvanishing
hypothesis is added and the two roots and both `hpow` data are carried through unchanged. -/
theorem exists_weilPairingMu_eq_inv_of_hprin_n {n : ℕ} [NeZero n]
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
      ∃ hpowST : weilPairingElt hS.left gT ^ n = 1,
        ∃ hpowTS : weilPairingElt hT.left gS ^ n = 1,
          weilPairingMu hS.left hpowST = (weilPairingMu hT.left hpowTS)⁻¹ := by
  obtain ⟨gS, gT, hgS, hgT, hcS, hcT, hpowST, hpowTS, hswap⟩ :=
    exists_weilPairingMu_mul_swap_eq_one_of_hprin_n hn hS hT hR hmS hmT hadd hPS hPT hprin
  exact ⟨gS, gT, hgS, hgT, hcS, hcT, hpowST, hpowTS, eq_inv_of_mul_eq_one_left hswap⟩

/-! ### The same two headlines over `F̄`, with no hypothesis beyond the setting -/

open Classical in
/-- **Antisymmetry of the Weil pairing in `μ_n(F)` at every `n` with `(2 : F) ≠ 0` and
`((n : ℤ) : F) ≠ 0`, over an algebraically closed field, with no hypothesis beyond the setting:**

```
μ_n(S, T) · μ_n(T, S) = 1      in rootsOfUnity n F.
```

The `hprin`-gated headline above with both of its gates discharged; neither discharge is new here
and both are `exists_weilPairingElt_mul_swap_eq_one_n_of_isAlgClosed`'s, through which this proof
routes.  This is the general-`n` form of `exists_weilPairingMu_mul_swap_eq_one_two` and
`exists_weilPairingMu_mul_swap_eq_one_three` (`WeilPairingProductRelationMu`).

⚠️ **`n ≠ 0` is not a hypothesis and must not be added**: `((n : ℤ) : F) ≠ 0` implies it, and the
index condition is the sharper of the two.  ⚠️ **`[NeZero n]` is bound even so, and is redundant as
a proposition** — `weilPairingMu` occurs in the conclusion and the instance is what lets it
elaborate, exactly as in `exists_weilPairingMu_divisorSlot_add_of_ne_zero_of_hprin`.  ⚠️ The
transcendence datum is `transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`, the term
`exists_gS_of_ne_zero_of_isAlgClosed` writes, **so a caller holding either statement's rung-5
certificate can `rw` with the other**. -/
theorem exists_weilPairingMu_mul_swap_eq_one_n_of_isAlgClosed [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    {n : ℕ} [NeZero n] (hnc : ((n : ℤ) : F) ≠ 0) {xS yS xT yT xR yR : F}
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
      ∃ hpowST : weilPairingElt hS.left gT ^ n = 1,
        ∃ hpowTS : weilPairingElt hT.left gS ^ n = 1,
          weilPairingMu hS.left hpowST * weilPairingMu hT.left hpowTS = 1 := by
  obtain ⟨gS, gT, hgS, hgT, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩, hswap⟩ :=
    exists_weilPairingElt_mul_swap_eq_one_n_of_isAlgClosed h2 hnc hS hT hR hmS hmT hadd
  have hpowST : weilPairingElt hS.left gT ^ n = 1 :=
    weilPairingElt_pow_eq_one_of_gS_n_torsion hS.left n
      (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hnc)
      (mem_torsion_iff.mp hmS) hgT huT
  have hpowTS : weilPairingElt hT.left gS ^ n = 1 :=
    weilPairingElt_pow_eq_one_of_gS_n_torsion hT.left n
      (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hnc)
      (mem_torsion_iff.mp hmT) hgS huS
  exact ⟨gS, gT, hgS, hgT, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩, hpowST, hpowTS,
    weilPairingMu_mul_swap_eq_one_of_weilPairingElt hS.left hT.left hpowST hpowTS hswap⟩

open Classical in
/-- **Antisymmetry in `μ_n(F)` in the quotable inverse form at every `n` with `(2 : F) ≠ 0` and
`((n : ℤ) : F) ≠ 0`, over an algebraically closed field**, with no hypothesis beyond the setting:
`μ_n(S, T) = (μ_n(T, S))⁻¹` in `rootsOfUnity n F`.  Immediate from the previous theorem, in the
group. -/
theorem exists_weilPairingMu_eq_inv_n_of_isAlgClosed [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    {n : ℕ} [NeZero n] (hnc : ((n : ℤ) : F) ≠ 0) {xS yS xT yT xR yR : F}
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
      ∃ hpowST : weilPairingElt hS.left gT ^ n = 1,
        ∃ hpowTS : weilPairingElt hT.left gS ^ n = 1,
          weilPairingMu hS.left hpowST = (weilPairingMu hT.left hpowTS)⁻¹ := by
  obtain ⟨gS, gT, hgS, hgT, hcS, hcT, hpowST, hpowTS, hswap⟩ :=
    exists_weilPairingMu_mul_swap_eq_one_n_of_isAlgClosed h2 hnc hS hT hR hmS hmT hadd
  exact ⟨gS, gT, hgS, hgT, hcS, hcT, hpowST, hpowTS, eq_inv_of_mul_eq_one_left hswap⟩

/-! ### Non-vacuity

⚠️ The certificate is run against the **`F̄` headline**, because it is the one with no gate; the two
`hprin`-gated headlines above are certified only through it, and that is said here rather than
papered over.

The curve is the shared `EllipticCurves.Fixture.y2EqX3SubX` over
`EllipticCurves.Fixture.AlgClosedQ` and the index is `n = 2`, which is
`WeilPairingProductRelationHprinN`'s own configuration: `(0, 0)`, `(1, 0)` and `(−1, 0)` are
`2`-torsion outright, with `(0, 0) ⊕ (1, 0) = (−1, 0)` and `S ≠ T`, so the instance is a genuine
instance of *antisymmetry* and not a disguised instance of the alternating property.  ⚠️ **The four
`example…Mu` lemmas below are this file's own and not that file's**, whose twins are `private` and
therefore unavailable across the module boundary; they are the same three `norm_num` discharges,
re-elaborated.
-/

section Nonvacuity

open EllipticCurves.Fixture

private lemma exampleTwoMu : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleNsSMu : (y2EqX3SubX AlgClosedQ).Nonsingular 0 0 :=
  (y2EqX3SubX AlgClosedQ).equation_iff_nonsingular.mp (by
    norm_num [y2EqX3SubX, WeierstrassCurve.Affine.equation_iff])

private lemma exampleNsTMu : (y2EqX3SubX AlgClosedQ).Nonsingular 1 0 :=
  (y2EqX3SubX AlgClosedQ).equation_iff_nonsingular.mp (by
    norm_num [y2EqX3SubX, WeierstrassCurve.Affine.equation_iff])

private lemma exampleNsRMu : (y2EqX3SubX AlgClosedQ).Nonsingular (-1) 0 :=
  (y2EqX3SubX AlgClosedQ).equation_iff_nonsingular.mp (by
    norm_num [y2EqX3SubX, WeierstrassCurve.Affine.equation_iff])

open Classical in
private lemma exampleTorSMu :
    Point.some (0 : AlgClosedQ) 0 exampleNsSMu ∈ (y2EqX3SubX AlgClosedQ).torsion 2 :=
  (mem_torsion_two_some_iff exampleNsSMu).mpr (by norm_num [y2EqX3SubX])

open Classical in
private lemma exampleTorTMu :
    Point.some (1 : AlgClosedQ) 0 exampleNsTMu ∈ (y2EqX3SubX AlgClosedQ).torsion 2 :=
  (mem_torsion_two_some_iff exampleNsTMu).mpr (by norm_num [y2EqX3SubX])

private lemma exampleAddMu :
    Point.some (0 : AlgClosedQ) 0 exampleNsSMu + Point.some (1 : AlgClosedQ) 0 exampleNsTMu
      = Point.some (-1 : AlgClosedQ) 0 exampleNsRMu := by
  rw [Point.add_of_X_ne (by norm_num)]
  simp only [Point.some.injEq]
  norm_num [y2EqX3SubX, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.negY]

private lemma exampleIndexMu : (((2 : ℕ) : ℤ) : AlgClosedQ) ≠ 0 := by norm_num

open Classical in
/-- **The general-`n` `μ_n(F)` antisymmetry headline, instantiated on a curve that exists**, at
`n = 2` and at two **distinct** named `2`-torsion points of `y² = x³ − x` over
`AlgebraicClosure ℚ`.  The conclusion lives in `rootsOfUnity 2 (AlgebraicClosure ℚ)`. -/
example : ∃ gS gT : (y2EqX3SubX AlgClosedQ).FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
    (∃ f : (y2EqX3SubX AlgClosedQ).FunctionField, f ≠ 0 ∧
      (y2EqX3SubX AlgClosedQ).divisor f
        = Finsupp.single (pointClosedPoint exampleNsSMu.left) ((2 : ℕ) : ℤ) ∧
      ∃ u : (y2EqX3SubX AlgClosedQ).CoordinateRingˣ,
        (u : (y2EqX3SubX AlgClosedQ).CoordinateRing) • gS ^ (2 : ℕ)
          = mulByNEndo 2 (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero
              exampleTwoMu exampleIndexMu) f) ∧
    (∃ f : (y2EqX3SubX AlgClosedQ).FunctionField, f ≠ 0 ∧
      (y2EqX3SubX AlgClosedQ).divisor f
        = Finsupp.single (pointClosedPoint exampleNsTMu.left) ((2 : ℕ) : ℤ) ∧
      ∃ u : (y2EqX3SubX AlgClosedQ).CoordinateRingˣ,
        (u : (y2EqX3SubX AlgClosedQ).CoordinateRing) • gT ^ (2 : ℕ)
          = mulByNEndo 2 (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero
              exampleTwoMu exampleIndexMu) f) ∧
    ∃ hpowST : weilPairingElt exampleNsSMu.left gT ^ (2 : ℕ) = 1,
      ∃ hpowTS : weilPairingElt exampleNsTMu.left gS ^ (2 : ℕ) = 1,
        weilPairingMu exampleNsSMu.left hpowST * weilPairingMu exampleNsTMu.left hpowTS = 1 :=
  exists_weilPairingMu_mul_swap_eq_one_n_of_isAlgClosed exampleTwoMu exampleIndexMu
    exampleNsSMu exampleNsTMu exampleNsRMu exampleTorSMu exampleTorTMu exampleAddMu

end Nonvacuity

end WeierstrassCurve.Affine
