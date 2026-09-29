/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.WeilPairingNondegenerateN
import EllipticCurves.FunctionField.WeilPairingSurjective
import EllipticCurves.FunctionField.WeilPairingTranslationSlotNondegenerate
import EllipticCurves.FunctionField.WeilPairingTranslationSlotNotInjective

/-!
# Non-degeneracy of the bundled map `e_n(S, ·) : E[n] → μ_n(F)` at a general index (rung 6)

`EllipticCurves.FunctionField.WeilPairingTranslationSlotHprinN` (`#1843`) bundles the translation
slot at **every** index,

```lean
weilPairingTorsionMuHom_n hn hg hu : Multiplicative (W.torsion n) →* rootsOfUnity n F,
```

and `EllipticCurves.FunctionField.WeilPairingTranslationSlotNondegenerate` (`#907`) says that the
bundled map is **not trivial** — but only at `n = 2` and `n = 3`.  This file removes the numeral.

⚠️ **Nothing new is proved here about curves.**  Every input of the non-triviality half is a merged
headline of `EllipticCurves.FunctionField.WeilPairingNondegenerateN`, exactly as the two-and-three
file was a restatement of `EllipticCurves.FunctionField.WeilPairingNondegenerateMu` one level
down; the two non-injectivity statements at the end consume two merged counts instead —
`card_torsion_eq_sq` and `natCard_rootsOfUnity_of_ne_zero` — and ⚠️ **both of those are already
general, which is the whole reason that row is a transcription and not a project** (see below).

## ⚠️ The object was general and only the statements about it were not

The row this file fills was the last gap in the rung-6 translation-slot family:

| property | `n = 2`, `n = 3` | general `n` |
| --- | --- | --- |
| the map exists | `weilPairingTorsionMuHom_{two,three}` | `weilPairingTorsionMuHom_n` |
| it is bilinear in the translation slot | `…TranslationSlotHprin` | `…TranslationSlotHprinN` |
| ⚠️ **it is not trivial** | `…TranslationSlotNondegenerate` | ⚠️ **this file** |
| it is not injective | `…TranslationSlotNotInjective` | ⚠️ **this file, for `1 < n`** |

`WeilPairingTranslationSlotNondegenerate`'s `## Scope` lists *"general `n`"* as out of scope.  That
bullet is not wrong about its own file and it is not edited here; what this file records is that
the reason it gave had already expired.  That module retires two earlier justifications for the
bullet — `#404`'s `ωₙ`, then `#251` — as *false*, and closes by observing that a general-`n` fibre
description *"no longer waits on that question"*.  It never re-measured the bullet against its own
observation.

## ⚠️ The gate structure is NOT the `n = 2` row's, and that is the one thing a reader must carry

`weilPairingTorsionMuHom_two_ne_one` binds `(2 : F) ≠ 0` and nothing else about the index.  The
general envelope `exists_torsion_n_weilPairingMu_ne_one` binds three index data, and they do
different jobs:

* `h2 : (2 : F) ≠ 0` — not about `n` at all; it is the characteristic condition the whole
  `weilPairingElt` layer runs under;
* `hn : ((n : ℤ) : F) ≠ 0` — the index condition proper;
* `hT : Transcendental F (n • genericPoint).xCoord` — ⚠️ **part of the TERM `mulByNEndo n hT` and
  not only of the hypothesis list**, which is why it is an explicit argument here as it is
  throughout `EllipticCurves.FunctionField.PullbackPrincipalityN`;
* `[NeZero n]`, which is what makes `rootsOfUnity n F` the right codomain.

⚠️ **Which transcendence proof is passed is a compatibility decision and not a detail** (`#909`,
`#2266`).  The `F̄` headline below writes
`transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn`, which is what
`exists_gS_of_ne_zero_of_isAlgClosed` writes, so a caller holding that rung-5 certificate can
`rw` with this one.  Every clause below reading *at every `n` with `(2 : F) ≠ 0` and
`((n : ℤ) : F) ≠ 0`* omits `hT` because it follows from exactly those two by that lemma; the
reach-clause exemption is recorded in `WeilPairingNondegenerateN`, which states the envelopes.

## ⚠️ Recovery splits into two classes, and only one of them is a `simpa`

The house form restates each merged twin verbatim and proves it *through* the general layer, so the
elaborator checks the generalisation rather than a reader taking it on faith.  Here the merged
headlines do not all recover the same way:

* `exists_weilPairingTorsionMuHom_{two,three}_ne_one` quantify the homomorphism **away**, so the
  recovery is `WeilPairingTranslationSlotHprinN`'s idiom — transport `hu` across `mulByNEndo_two`
  and cast the divisor coefficient, because the general form writes `((2 : ℕ) : ℤ)` where the
  merged statement writes `(2 : ℤ)`.
* ⚠️ The other three name `weilPairingTorsionMuHom_two h2 hg hu` **in the statement**, and `hu`'s
  own type differs — `… = mulByTwoEndo h2 f` against `… = mulByNEndo 2 _ f`, only *propositionally*
  equal.  No `simpa` reaches that.  What does is `weilPairingTorsionMuHom_two_eq_n` below, and
  ⚠️ **it is `rfl`**: the two definitions are one expression with the numeral substituted,
  `(weilPairingPointMuHom hg k).comp (AddMonoidHom.toMultiplicative (AddSubgroup.inclusion P))`,
  and their only differing argument `P` is a proof of a `≤`.  `NeZero` and `Transcendental` are
  `Prop` too, so those differ irrelevantly as well.

That congruence is stated **publicly** rather than inlined into the recovery proofs: it is the
bridge a consumer holding a merged `weilPairingTorsionMuHom_two` needs in order to apply anything
proved here, and it is the only route between the two objects.

## ⚠️ Non-injectivity at a general index is here too, and the count it needs is merged

`EllipticCurves.FunctionField.WeilPairingTranslationSlotNotInjective` refutes injectivity of
`e_n(S, ·)` by counting: `#E[n] = n²` over `F̄` against `#μ_n(F̄) = n`, and `n² > n`.  Both counts
are general.  `card_torsion_eq_sq` (`EllipticCurves.Torsion.StructureGeneral`, `#293`) is
`#E[n] = n²` **at every `n`** under `(2 : F) ≠ 0` and `(n : F) ≠ 0`, with no smoothness, Ward or
parity gate — the gated lemma is the *other* one, `card_torsion_eq_sq_of_smooth` — and
`natCard_rootsOfUnity_of_ne_zero` (`EllipticCurves.FunctionField.WeilPairingSurjective`) is
`#μ_n(F̄) = n` under the same index condition.  So the general-`n` row of that file is a
**transcription**, and it is taken below.

⚠️ **The only new datum is `1 < n`, and it is a genuine side condition rather than a counting
input**: at `n = 1` both groups are trivial, `1² = 1`, and the map really is injective.  The two
merged numerals do not bind it because `2` and `3` discharge it by `decide`.

⚠️ **An earlier draft of this docstring asserted the opposite** — that `#E[n] = n²` at a general
`n` is *"the Ward gate and is not available here"*, and that the row was missing a counting input.
Both clauses were false, and the second was false inside this file's own import closure:
`EllipticCurves.Torsion.StructureGeneral` is in it, and `exists_nonsingular_mem_torsion`
(`EllipticCurves.FunctionField.PullbackPrincipalityN`), which this file's own `section Nonvacuity`
calls, already proves its `#E[n] = n²` step by `card_torsion_eq_sq`.  ⚠️ **The tree had retired
that same claim once already**, at `EllipticCurves.FunctionField.MulByNGalois`, whose `n = 5`
bullet reads *"Neither clause is true any more: the count is `card_torsion_eq_sq` at every `n` …
(`#293`)"*.  It is recorded here because a false *"this is blocked on a missing input"* is the one
direction nothing downstream catches: a later round reads it and does not attempt a row that is
four proof lines away.  ⚠️ **`#1184` is division-polynomial coprimality over an arbitrary
commutative ring; it is not this count and does not gate it.**

## Main results

* `weilPairingTorsionMuHom_n_apply_some` — the value rule at a general index, **ungated**, and
  `rfl` for the reason `WeilPairingTranslationSlotNondegenerate` gives at length;
* `weilPairingTorsionMuHom_two_eq_n`, `weilPairingTorsionMuHom_three_eq_n` — the merged objects
  **are** the general one at their index, also `rfl`;
* `weilPairingTorsionMuHom_n_ne_one` — the map is not the trivial homomorphism;
* `ker_weilPairingTorsionMuHom_n_ne_top` — its kernel is a proper subgroup of `E[n]`;
* `eq_zero_of_weilPairingTorsionMuHom_n_eq_one` — **Silverman III.8.1(c) at every index, as one
  equation of homomorphisms**: `e_n(S, ·) = 1` forces `S = O`.  The gain over
  `eq_zero_of_forall_weilPairingMu_eq_one_n` is that a four-binder `∀` — including the `hpow`
  binder `WeilPairingNondegenerateMu` spends a docstring section apologising for — collapses to
  `φ = 1`;
* `exists_weilPairingTorsionMuHom_n_ne_one` — over `F̄`, with no hypothesis beyond `(2 : F) ≠ 0`
  and `((n : ℤ) : F) ≠ 0`: `e_n(S, ·) : E[n] → μ_n(F̄)` **is a non-trivial group homomorphism at
  every such index**;
* `not_injective_weilPairingTorsionMuHom_n`, `ker_weilPairingTorsionMuHom_n_ne_bot` — and at every
  index with `1 < n` it is **not** injective, by the counting argument above.  The general forms of
  `EllipticCurves.FunctionField.WeilPairingTranslationSlotNotInjective`'s two pairs.

## Scope

`[Field F] {W : Affine F} [W.IsElliptic]`.  The value rule and the two congruences are ungated.
Everything else inherits `[IsAlgClosed F]` from the `WeilPairingNondegenerateN` envelopes and
**from nowhere else** — the single source is `hprin`, i.e. `exists_gS_n_of_isAlgClosed` (`#1843`),
as for every other `[IsAlgClosed F]` on this front.  No hypothesis is added to any envelope: only
the conclusions move.

Out of scope, each for a stated reason rather than for room: an `hprin`-gated arbitrary-field form
of the `≠ 1` headlines — `WeilPairingNondegenerateN` binds
`[IsAlgClosed F]` on its whole `Nondegenerate` section, so there is no arbitrary-field
non-degeneracy envelope to consume, and `exists_weilPairingTorsionMuHom_n_of_hprin` therefore
cannot simply acquire a `φ ≠ 1` conjunct; combining the two slots into a pairing on
`W.Point × W.Point`, which `#873`/`#890` both record as a separate design question.  Nothing
existing is renamed or reproved: this module is purely additive.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8, Prop. 8.1(c).
-/

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic] {x y : F}

/-! ### The value rule, and the two merged objects identified with this one -/

open Classical in
/-- **The value of the bundled map at an affine torsion point, at every index** is the merged
`weilPairingMu`.  The general-`n` form of `weilPairingTorsionMuHom_{two,three}_apply_some`, and
`rfl` for the same reason: `weilPairingPointMu` and `weilPairingMu` are `Classical.choose` of two
different existence proofs whose affine branches are the same term, and proof-irrelevance in the
`hpow` slot absorbs the mismatched datum.

⚠️ Not a `simp` lemma: `hpow` appears on the right and not on the left. -/
theorem weilPairingTorsionMuHom_n_apply_some {n : ℕ} [NeZero n]
    (hT : Transcendental F (n • genericPoint (W := W)).xCoord) {f gS : W.FunctionField}
    {u : W.CoordinateRingˣ} (hgS : gS ≠ 0)
    (hu : (u : W.CoordinateRing) • gS ^ n = mulByNEndo n hT f)
    (hₙ : W.Nonsingular x y) (hmem : Point.some x y hₙ ∈ W.torsion n)
    (hpow : weilPairingElt hₙ.left gS ^ n = 1) :
    weilPairingTorsionMuHom_n hT hgS hu
        (Multiplicative.ofAdd (⟨Point.some x y hₙ, hmem⟩ : W.torsion n))
      = weilPairingMu hₙ.left hpow :=
  rfl

open Classical in
/-- **The merged `n = 2` homomorphism *is* the general one at `n = 2`.**

`rfl`: the two definitions are both
`(weilPairingPointMuHom hg 2).comp (AddMonoidHom.toMultiplicative (AddSubgroup.inclusion P))`
with different `P`, and `P` is a proof of a `≤`.

⚠️ The two rung-5 certificates `hu` and `hu'` say the same thing about the same `gS` in the two
spellings of `[2]∗` — they are interchangeable by `mulByNEndo_two` but not *definitionally*, which
is why both are arguments rather than one being derived in the statement. -/
theorem weilPairingTorsionMuHom_two_eq_n (h2 : (2 : F) ≠ 0) {f gS : W.FunctionField}
    {u : W.CoordinateRingˣ} (hgS : gS ≠ 0)
    (hu : (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f)
    (hu' : (u : W.CoordinateRing) • gS ^ 2
      = mulByNEndo 2 (transcendental_xCoord_two_nsmul (W := W) h2) f) :
    weilPairingTorsionMuHom_two h2 hgS hu
      = weilPairingTorsionMuHom_n (transcendental_xCoord_two_nsmul (W := W) h2) hgS hu' :=
  rfl

open Classical in
/-- **The merged `n = 3` homomorphism *is* the general one at `n = 3`**, the mirror of
`weilPairingTorsionMuHom_two_eq_n` and equally `rfl`. -/
theorem weilPairingTorsionMuHom_three_eq_n (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {f gS : W.FunctionField} {u : W.CoordinateRingˣ} (hgS : gS ≠ 0)
    (hu : (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f)
    (hu' : (u : W.CoordinateRing) • gS ^ 3
      = mulByNEndo 3 (transcendental_xCoord_three_nsmul (W := W) h2 h3) f) :
    weilPairingTorsionMuHom_three h2 h3 hgS hu
      = weilPairingTorsionMuHom_n (transcendental_xCoord_three_nsmul (W := W) h2 h3) hgS hu' :=
  rfl

section IsAlgClosed

variable [IsAlgClosed F]

/-! ### The three pointwise headlines at every index -/

open Classical in
/-- **The bundled pairing map is not the trivial homomorphism, at every index.**

```
e_n(S, ·) : E[n] → μ_n(F) is not 1.
```

The envelope is `exists_torsion_n_weilPairingMu_ne_one`'s, **unchanged**: same principal `f_S` with
`div f_S = n·(S)`, same rung-5 certificate `hu`.  Only the conclusion moves — the affine witness
`T` that file exhibits is quantified away, and what is left is a statement about the map.

⚠️ `hT` pays for the term `mulByNEndo n hT`; `hn` pays for the non-degeneracy; `h2` pays for the
`weilPairingElt` layer underneath both.  None of the three is interchangeable with another. -/
theorem weilPairingTorsionMuHom_n_ne_one {n : ℕ} [NeZero n] (h2 : (2 : F) ≠ 0)
    (hn : ((n : ℤ) : F) ≠ 0) (hT : Transcendental F (n • genericPoint (W := W)).xCoord)
    (h : W.Nonsingular x y) {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ))
    (hgS : gS ≠ 0) {u : W.CoordinateRingˣ}
    (hu : (u : W.CoordinateRing) • gS ^ n = mulByNEndo n hT f) :
    weilPairingTorsionMuHom_n hT hgS hu ≠ 1 := by
  obtain ⟨xₙ, yₙ, hₙ, hmem, hpow, hne⟩ :=
    exists_torsion_n_weilPairingMu_ne_one h2 hn hT h hf hfdiv hgS hu
  refine fun hone => hne ?_
  have hval := DFunLike.congr_fun hone
    (Multiplicative.ofAdd (⟨Point.some xₙ yₙ hₙ, hmem⟩ : W.torsion n))
  rwa [weilPairingTorsionMuHom_n_apply_some hT hgS hu hₙ hmem hpow] at hval

open Classical in
/-- **The kernel of the bundled map is a proper subgroup of `E[n]`**, at every index: some
`n`-torsion point does not pair trivially with `S`.  The `MonoidHom.ker` form of
`weilPairingTorsionMuHom_n_ne_one`. -/
theorem ker_weilPairingTorsionMuHom_n_ne_top {n : ℕ} [NeZero n] (h2 : (2 : F) ≠ 0)
    (hn : ((n : ℤ) : F) ≠ 0) (hT : Transcendental F (n • genericPoint (W := W)).xCoord)
    (h : W.Nonsingular x y) {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ))
    (hgS : gS ≠ 0) {u : W.CoordinateRingˣ}
    (hu : (u : W.CoordinateRing) • gS ^ n = mulByNEndo n hT f) :
    MonoidHom.ker (weilPairingTorsionMuHom_n hT hgS hu) ≠ ⊤ := by
  obtain ⟨xₙ, yₙ, hₙ, hmem, hpow, hne⟩ :=
    exists_torsion_n_weilPairingMu_ne_one h2 hn hT h hf hfdiv hgS hu
  refine fun htop => hne ?_
  have hval : (Multiplicative.ofAdd (⟨Point.some xₙ yₙ hₙ, hmem⟩ : W.torsion n))
      ∈ MonoidHom.ker (weilPairingTorsionMuHom_n hT hgS hu) := htop ▸ Subgroup.mem_top _
  rw [MonoidHom.mem_ker, weilPairingTorsionMuHom_n_apply_some hT hgS hu hₙ hmem hpow] at hval
  exact hval

open Classical in
/-- **Silverman III.8.1(c) at every index, as a statement about the map**: if `e_n(S, ·)` is the
trivial homomorphism then `S = O`.

⚠️ Compare `eq_zero_of_forall_weilPairingMu_eq_one_n`, whose trivial-pairing hypothesis is a `∀`
over `xₙ yₙ hₙ`, over torsion membership **and over `hpow`**.  Here it is the single equation
`φ = 1`.  That is the whole gain from bundling, and it is why the binder apology in
`WeilPairingNondegenerateMu`'s docstring does not have to be repeated at a general index either.

⚠️ `S : W.Point` is arbitrary and the divisor condition is written with `pointDivisorAff`, which is
`n`-free and sends `O` to `0`, so no case split appears in the statement. -/
theorem eq_zero_of_weilPairingTorsionMuHom_n_eq_one {n : ℕ} [NeZero n] (h2 : (2 : F) ≠ 0)
    (hn : ((n : ℤ) : F) ≠ 0) (hT : Transcendental F (n • genericPoint (W := W)).xCoord)
    {S : W.Point} {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = (n : ℤ) • pointDivisorAff W S) (hgS : gS ≠ 0)
    {u : W.CoordinateRingˣ} (hu : (u : W.CoordinateRing) • gS ^ n = mulByNEndo n hT f)
    (hone : weilPairingTorsionMuHom_n hT hgS hu = 1) :
    S = 0 := by
  refine eq_zero_of_forall_weilPairingMu_eq_one_n h2 hn hT hf hfdiv hgS hu
    fun xₙ yₙ hₙ hmem hpow => ?_
  have hval := DFunLike.congr_fun hone
    (Multiplicative.ofAdd (⟨Point.some xₙ yₙ hₙ, hmem⟩ : W.torsion n))
  rwa [weilPairingTorsionMuHom_n_apply_some hT hgS hu hₙ hmem hpow] at hval

/-! ### And it is never injective, at every index with `1 < n` -/

open Classical in
/-- **The bundled pairing map is never injective, at every index with `1 < n`**, for every `S`,
every rung-5 root and every certificate.  The general form of
`not_injective_weilPairingTorsionMuHom_{two,three}`
(`EllipticCurves.FunctionField.WeilPairingTranslationSlotNotInjective`), by the same argument:
`#E[n] = n²` over `F̄` (`card_torsion_eq_sq`, `#293`) against `#μ_n(F̄) = n`
(`natCard_rootsOfUnity_of_ne_zero`), and an injection would force `n² ≤ n`.

⚠️ Nothing about non-degeneracy is used, and none of the envelope data is: this holds of *any*
`weilPairingTorsionMuHom_n`, which is why the hypothesis list is the object's and not the
envelope's.  ⚠️ `1 < n` is not a counting input — at `n = 1` both sides have one element and the
map is injective — and it is the only thing the merged numerals get for free. -/
theorem not_injective_weilPairingTorsionMuHom_n {n : ℕ} [NeZero n] (h2 : (2 : F) ≠ 0)
    (hn : ((n : ℤ) : F) ≠ 0) (hlt : 1 < n)
    (hT : Transcendental F (n • genericPoint (W := W)).xCoord) {f gS : W.FunctionField}
    {u : W.CoordinateRingˣ} (hgS : gS ≠ 0)
    (hu : (u : W.CoordinateRing) • gS ^ n = mulByNEndo n hT f) :
    ¬ Function.Injective (weilPairingTorsionMuHom_n hT hgS hu) := fun hinj => by
  have hn' : (n : F) ≠ 0 := by rwa [Int.cast_natCast] at hn
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_congr Multiplicative.toAdd, card_torsion_eq_sq h2 hn',
    natCard_rootsOfUnity_of_ne_zero (F := F) (n := n) hn'] at hle
  nlinarith

open Classical in
/-- **The kernel of the bundled map is not the trivial subgroup**, at every index with `1 < n`:
the `MonoidHom.ker` form of `not_injective_weilPairingTorsionMuHom_n`, and the companion of
`ker_weilPairingTorsionMuHom_n_ne_top` above — the kernel is a *proper* subgroup of `E[n]` and it
is *not* `⊥`. -/
theorem ker_weilPairingTorsionMuHom_n_ne_bot {n : ℕ} [NeZero n] (h2 : (2 : F) ≠ 0)
    (hn : ((n : ℤ) : F) ≠ 0) (hlt : 1 < n)
    (hT : Transcendental F (n • genericPoint (W := W)).xCoord) {f gS : W.FunctionField}
    {u : W.CoordinateRingˣ} (hgS : gS ≠ 0)
    (hu : (u : W.CoordinateRing) • gS ^ n = mulByNEndo n hT f) :
    MonoidHom.ker (weilPairingTorsionMuHom_n hT hgS hu) ≠ ⊥ := fun hbot =>
  not_injective_weilPairingTorsionMuHom_n h2 hn hlt hT hgS hu
    (MonoidHom.ker_eq_bot_iff _ |>.mp hbot)

end IsAlgClosed

end CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

open CoordinateRing

section IsAlgClosed

variable [IsAlgClosed F]

/-! ### Over `F̄`, with no hypothesis beyond the setting -/

open Classical in
/-- **`e_n(S, ·) : E[n] → μ_n(F̄)` is a *non-trivial* group homomorphism at every `n` with
`((n : ℤ) : F) ≠ 0`, with no hypothesis beyond the setting.**

The shape `exists_weilPairingTorsionMuHom_of_ne_zero_of_hprin`
(`WeilPairingTranslationSlotHprinN`) returns, with the `φ ≠ 1` conjunct added, so the two compose
rather than diverge — the same move `exists_weilPairingTorsionMuHom_two_ne_one` made on `#890`'s
shape.  The rung-5 certificate is produced by `exists_gS_of_ne_zero_of_isAlgClosed` (`#1843`),
which is the only place `[IsAlgClosed F]` enters.

⚠️ `[NeZero n]` is **derived** from `hn` rather than bound: `((n : ℤ) : F) ≠ 0` already rules out
`n = 0`, and **nothing in this statement forces the instance**: the conclusion names only the bare
type `Multiplicative (W.torsion n) →* rootsOfUnity n F`, never `weilPairingTorsionMuHom_n`, and it
is that definition — not `rootsOfUnity` — which binds `[NeZero n]`.  ⚠️ **That mechanism, and not
the redundancy, is the reason.**  Where a statement *does* name such an object the instance is
forced, the pair must be bound, and `#2266` r3 ruled that binding **correct** — *"`[NeZero n]`
alongside `((n : ℤ) : F) ≠ 0` is CORRECT … do not open a round to strip it"*.  Every theorem above
this one names `weilPairingTorsionMuHom_n` and binds both, for exactly that reason. -/
theorem exists_weilPairingTorsionMuHom_n_ne_one (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0) {xS yS : F} (hS : W.Nonsingular xS yS)
    (hmS : Point.some xS yS hS ∈ W.torsion n) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn) f) ∧
      ∃ φ : Multiplicative (W.torsion n) →* rootsOfUnity n F, φ ≠ 1 ∧
        ∀ P : W.torsion n,
          algebraMap F W.FunctionField ((φ (Multiplicative.ofAdd P) : Fˣ) : F)
            = weilPairingPointElt g (P : W.Point) := by
  have : NeZero n := ⟨(by rintro rfl; simp at hn)⟩
  obtain ⟨f, hf, hd, g, hg, u, hu⟩ := exists_gS_of_ne_zero_of_isAlgClosed h2 hn hS hmS
  exact ⟨g, hg, ⟨f, hf, hd, u, hu⟩,
    weilPairingTorsionMuHom_n _ hg hu,
    weilPairingTorsionMuHom_n_ne_one h2 hn _ hS hf hd hg hu,
    fun P => algebraMap_coe_weilPairingTorsionMuHom_n _ hg hu P⟩

end IsAlgClosed

/-! ### Recovery of the merged numeral layer, compiled

⚠️ **The containment is committed here rather than asserted in a docstring**, following
`EllipticCurves.FunctionField.PullbackPrincipalityN` and
`EllipticCurves.FunctionField.WeilPairingNondegenerateN`, which do the same on their fronts.  Each
statement below is its merged twin **verbatim** and is proved *through* the general layer.

⚠️ All twelve are `private`: public copies would duplicate merged names.  ⚠️ **The last four are
`WeilPairingTranslationSlotNotInjective`'s**, and they are the reason this module imports that file
at all: its three imports are already this module's, so taking it costs **one** module in the
closure and keeps the house form whole, where dropping the recovery would have cost a paragraph
explaining why.  ⚠️ They are also the only four whose merged statements bind **no** index
condition, so each supplies `1 < n` by `norm_num` — the whole of what the numeral buys there.

⚠️ **`WeilPairingTranslationSlotNondegenerate` `omit`s nothing from its ambient block** and
declares exactly `variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic] {x y : F}` plus
`[IsAlgClosed F]` inside its `IsAlgClosed` sections — checked against its `omit` lines and not by
comparing signature strings, because a recovery that quietly keeps an instance its original omits
restates something *weaker* than the theorem it claims to subsume, and the signatures match either
way. -/

section Recovery

variable [IsAlgClosed F] {x y : F}

open Classical in
/-- `weilPairingTorsionMuHom_two_ne_one`, recovered through `weilPairingTorsionMuHom_two_eq_n`. -/
private theorem weilPairingTorsionMuHom_two_ne_one_of_general (h2 : (2 : F) ≠ 0)
    (h : W.Nonsingular x y) {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ))
    (hgS : gS ≠ 0) {u : W.CoordinateRingˣ}
    (hu : (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f) :
    weilPairingTorsionMuHom_two h2 hgS hu ≠ 1 := by
  have hu' : (u : W.CoordinateRing) • gS ^ 2
      = mulByNEndo 2 (transcendental_xCoord_two_nsmul (W := W) h2) f := by
    rw [hu, ← mulByNEndo_two h2]
  rw [weilPairingTorsionMuHom_two_eq_n h2 hgS hu hu']
  exact weilPairingTorsionMuHom_n_ne_one h2 (by exact_mod_cast h2) _ h hf
    (by exact_mod_cast hfdiv) hgS hu'

open Classical in
/-- `weilPairingTorsionMuHom_three_ne_one`, recovered. -/
private theorem weilPairingTorsionMuHom_three_ne_one_of_general (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (h : W.Nonsingular x y) {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ))
    (hgS : gS ≠ 0) {u : W.CoordinateRingˣ}
    (hu : (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f) :
    weilPairingTorsionMuHom_three h2 h3 hgS hu ≠ 1 := by
  have hu' : (u : W.CoordinateRing) • gS ^ 3
      = mulByNEndo 3 (transcendental_xCoord_three_nsmul (W := W) h2 h3) f := by
    rw [hu, ← mulByNEndo_three h2 h3]
  rw [weilPairingTorsionMuHom_three_eq_n h2 h3 hgS hu hu']
  exact weilPairingTorsionMuHom_n_ne_one h2 (by exact_mod_cast h3) _ h hf
    (by exact_mod_cast hfdiv) hgS hu'

open Classical in
/-- `ker_weilPairingTorsionMuHom_two_ne_top`, recovered. -/
private theorem ker_weilPairingTorsionMuHom_two_ne_top_of_general (h2 : (2 : F) ≠ 0)
    (h : W.Nonsingular x y) {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ))
    (hgS : gS ≠ 0) {u : W.CoordinateRingˣ}
    (hu : (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f) :
    MonoidHom.ker (weilPairingTorsionMuHom_two h2 hgS hu) ≠ ⊤ := by
  have hu' : (u : W.CoordinateRing) • gS ^ 2
      = mulByNEndo 2 (transcendental_xCoord_two_nsmul (W := W) h2) f := by
    rw [hu, ← mulByNEndo_two h2]
  rw [weilPairingTorsionMuHom_two_eq_n h2 hgS hu hu']
  exact ker_weilPairingTorsionMuHom_n_ne_top h2 (by exact_mod_cast h2) _ h hf
    (by exact_mod_cast hfdiv) hgS hu'

open Classical in
/-- `ker_weilPairingTorsionMuHom_three_ne_top`, recovered. -/
private theorem ker_weilPairingTorsionMuHom_three_ne_top_of_general (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (h : W.Nonsingular x y) {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ))
    (hgS : gS ≠ 0) {u : W.CoordinateRingˣ}
    (hu : (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f) :
    MonoidHom.ker (weilPairingTorsionMuHom_three h2 h3 hgS hu) ≠ ⊤ := by
  have hu' : (u : W.CoordinateRing) • gS ^ 3
      = mulByNEndo 3 (transcendental_xCoord_three_nsmul (W := W) h2 h3) f := by
    rw [hu, ← mulByNEndo_three h2 h3]
  rw [weilPairingTorsionMuHom_three_eq_n h2 h3 hgS hu hu']
  exact ker_weilPairingTorsionMuHom_n_ne_top h2 (by exact_mod_cast h3) _ h hf
    (by exact_mod_cast hfdiv) hgS hu'

open Classical in
/-- `eq_zero_of_weilPairingTorsionMuHom_two_eq_one`, recovered.  ⚠️ This is the one whose
hypothesis is the equation itself, so the congruence has to be used *contravariantly* — on `hone`
and not on the goal. -/
private theorem eq_zero_of_weilPairingTorsionMuHom_two_eq_one_of_general (h2 : (2 : F) ≠ 0)
    {S : W.Point} {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = (2 : ℤ) • pointDivisorAff W S) (hgS : gS ≠ 0)
    {u : W.CoordinateRingˣ} (hu : (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f)
    (hone : weilPairingTorsionMuHom_two h2 hgS hu = 1) :
    S = 0 := by
  have hu' : (u : W.CoordinateRing) • gS ^ 2
      = mulByNEndo 2 (transcendental_xCoord_two_nsmul (W := W) h2) f := by
    rw [hu, ← mulByNEndo_two h2]
  rw [weilPairingTorsionMuHom_two_eq_n h2 hgS hu hu'] at hone
  exact eq_zero_of_weilPairingTorsionMuHom_n_eq_one h2 (by exact_mod_cast h2) _ hf
    (by exact_mod_cast hfdiv) hgS hu' hone

open Classical in
/-- `eq_zero_of_weilPairingTorsionMuHom_three_eq_one`, recovered. -/
private theorem eq_zero_of_weilPairingTorsionMuHom_three_eq_one_of_general (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {S : W.Point} {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = (3 : ℤ) • pointDivisorAff W S) (hgS : gS ≠ 0)
    {u : W.CoordinateRingˣ} (hu : (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f)
    (hone : weilPairingTorsionMuHom_three h2 h3 hgS hu = 1) :
    S = 0 := by
  have hu' : (u : W.CoordinateRing) • gS ^ 3
      = mulByNEndo 3 (transcendental_xCoord_three_nsmul (W := W) h2 h3) f := by
    rw [hu, ← mulByNEndo_three h2 h3]
  rw [weilPairingTorsionMuHom_three_eq_n h2 h3 hgS hu hu'] at hone
  exact eq_zero_of_weilPairingTorsionMuHom_n_eq_one h2 (by exact_mod_cast h3) _ hf
    (by exact_mod_cast hfdiv) hgS hu' hone

open Classical in
/-- `exists_weilPairingTorsionMuHom_two_ne_one`, recovered.  ⚠️ The homomorphism is quantified
away here, so this is the `simpa` class and needs no congruence. -/
private theorem exists_weilPairingTorsionMuHom_two_ne_one_of_general (h2 : (2 : F) ≠ 0)
    {xS yS : F} (hS : W.Nonsingular xS yS) (hmS : Point.some xS yS hS ∈ W.torsion 2) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
      ∃ φ : Multiplicative (W.torsion 2) →* rootsOfUnity 2 F, φ ≠ 1 ∧
        ∀ P : W.torsion 2,
          algebraMap F W.FunctionField ((φ (Multiplicative.ofAdd P) : Fˣ) : F)
            = weilPairingPointElt g (P : W.Point) := by
  have key := exists_weilPairingTorsionMuHom_n_ne_one (W := W) (n := 2) h2
    (by exact_mod_cast h2) hS hmS
  simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using key

open Classical in
/-- `exists_weilPairingTorsionMuHom_three_ne_one`, recovered. -/
private theorem exists_weilPairingTorsionMuHom_three_ne_one_of_general (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {xS yS : F} (hS : W.Nonsingular xS yS)
    (hmS : Point.some xS yS hS ∈ W.torsion 3) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) ∧
      ∃ φ : Multiplicative (W.torsion 3) →* rootsOfUnity 3 F, φ ≠ 1 ∧
        ∀ P : W.torsion 3,
          algebraMap F W.FunctionField ((φ (Multiplicative.ofAdd P) : Fˣ) : F)
            = weilPairingPointElt g (P : W.Point) := by
  have key := exists_weilPairingTorsionMuHom_n_ne_one (W := W) (n := 3) h2
    (by exact_mod_cast h3) hS hmS
  simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using key

open Classical in
/-- `not_injective_weilPairingTorsionMuHom_two`
(`EllipticCurves.FunctionField.WeilPairingTranslationSlotNotInjective`), recovered.  ⚠️ The merged
statement binds no `1 < n` and the general one does; here it is `by norm_num`, which is the whole
of what the numeral buys. -/
private theorem not_injective_weilPairingTorsionMuHom_two_of_general (h2 : (2 : F) ≠ 0)
    {f gS : W.FunctionField} {u : W.CoordinateRingˣ} (hgS : gS ≠ 0)
    (hu : (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f) :
    ¬ Function.Injective (weilPairingTorsionMuHom_two h2 hgS hu) := by
  have hu' : (u : W.CoordinateRing) • gS ^ 2
      = mulByNEndo 2 (transcendental_xCoord_two_nsmul (W := W) h2) f := by
    rw [hu, ← mulByNEndo_two h2]
  rw [weilPairingTorsionMuHom_two_eq_n h2 hgS hu hu']
  exact not_injective_weilPairingTorsionMuHom_n h2 (by exact_mod_cast h2) (by norm_num) _ hgS hu'

open Classical in
/-- `not_injective_weilPairingTorsionMuHom_three`, recovered. -/
private theorem not_injective_weilPairingTorsionMuHom_three_of_general (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {f gS : W.FunctionField} {u : W.CoordinateRingˣ} (hgS : gS ≠ 0)
    (hu : (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f) :
    ¬ Function.Injective (weilPairingTorsionMuHom_three h2 h3 hgS hu) := by
  have hu' : (u : W.CoordinateRing) • gS ^ 3
      = mulByNEndo 3 (transcendental_xCoord_three_nsmul (W := W) h2 h3) f := by
    rw [hu, ← mulByNEndo_three h2 h3]
  rw [weilPairingTorsionMuHom_three_eq_n h2 h3 hgS hu hu']
  exact not_injective_weilPairingTorsionMuHom_n h2 (by exact_mod_cast h3) (by norm_num) _ hgS hu'

open Classical in
/-- `ker_weilPairingTorsionMuHom_two_ne_bot`, recovered. -/
private theorem ker_weilPairingTorsionMuHom_two_ne_bot_of_general (h2 : (2 : F) ≠ 0)
    {f gS : W.FunctionField} {u : W.CoordinateRingˣ} (hgS : gS ≠ 0)
    (hu : (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f) :
    MonoidHom.ker (weilPairingTorsionMuHom_two h2 hgS hu) ≠ ⊥ := by
  have hu' : (u : W.CoordinateRing) • gS ^ 2
      = mulByNEndo 2 (transcendental_xCoord_two_nsmul (W := W) h2) f := by
    rw [hu, ← mulByNEndo_two h2]
  rw [weilPairingTorsionMuHom_two_eq_n h2 hgS hu hu']
  exact ker_weilPairingTorsionMuHom_n_ne_bot h2 (by exact_mod_cast h2) (by norm_num) _ hgS hu'

open Classical in
/-- `ker_weilPairingTorsionMuHom_three_ne_bot`, recovered. -/
private theorem ker_weilPairingTorsionMuHom_three_ne_bot_of_general (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {f gS : W.FunctionField} {u : W.CoordinateRingˣ} (hgS : gS ≠ 0)
    (hu : (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f) :
    MonoidHom.ker (weilPairingTorsionMuHom_three h2 h3 hgS hu) ≠ ⊥ := by
  have hu' : (u : W.CoordinateRing) • gS ^ 3
      = mulByNEndo 3 (transcendental_xCoord_three_nsmul (W := W) h2 h3) f := by
    rw [hu, ← mulByNEndo_three h2 h3]
  rw [weilPairingTorsionMuHom_three_eq_n h2 h3 hgS hu hu']
  exact ker_weilPairingTorsionMuHom_n_ne_bot h2 (by exact_mod_cast h3) (by norm_num) _ hgS hu'

end Recovery

/-! ### Non-vacuity at an index outside `{2, 3}`

⚠️ **A certificate at `n = 2` or `n = 3` would prove nothing that
`WeilPairingTranslationSlotNondegenerate`
does not**, so the witness is produced at an index neither of them reaches.  `#1843`'s
`exists_nonsingular_mem_torsion` supplies one over `F̄` at every `n ≠ 0, 1` with `(2 : F) ≠ 0` and
`(n : F) ≠ 0`; ⚠️ **naming the index condition alone would be false and not merely partial** — at
`n = char F` the index condition holds and no affine `n`-torsion point is supplied, because
`#E[n] = n²` is *false* there, which is `PullbackPrincipalityN`'s own wording.

⚠️ **The point is not nameable at `n = 5`**, so the certificate is stated at a *quantified* `(x, y)`
rather than exhibiting coordinates the way the merged numeral file exhibits `(0, 0)`. -/

section Nonvacuity

/-! The certificate curve `y² + y = x³` is the shared `EllipticCurves.Fixture.y2AddYEqX3` and the
base — algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `5 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here. -/

open EllipticCurves.Fixture

open Classical in
/-- **A non-trivial `e_5(S, ·) : E[5] → μ_5(F̄)` on a curve that exists**, over
`AlgebraicClosure ℚ`: the headline at an index neither merged numeral file reaches.  ⚠️ The
`5`-torsion divisor point `S` is produced by `exists_nonsingular_mem_torsion` and not exhibited. -/
example : ∃ (xS yS : AlgClosedQ) (hS : (y2AddYEqX3 AlgClosedQ).Nonsingular xS yS),
    ∃ g : (y2AddYEqX3 AlgClosedQ).FunctionField, g ≠ 0 ∧
      (∃ f : (y2AddYEqX3 AlgClosedQ).FunctionField, f ≠ 0 ∧
        (y2AddYEqX3 AlgClosedQ).divisor f
          = Finsupp.single (pointClosedPoint hS.left) (5 : ℤ) ∧
        ∃ u : (y2AddYEqX3 AlgClosedQ).CoordinateRingˣ,
          (u : (y2AddYEqX3 AlgClosedQ).CoordinateRing) • g ^ 5
            = mulByNEndo 5 (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero
                (W := y2AddYEqX3 AlgClosedQ) (by norm_num) (by norm_num)) f) ∧
      ∃ φ : Multiplicative ((y2AddYEqX3 AlgClosedQ).torsion 5) →* rootsOfUnity 5 AlgClosedQ,
        φ ≠ 1 ∧ ∀ P : (y2AddYEqX3 AlgClosedQ).torsion 5,
          algebraMap AlgClosedQ (y2AddYEqX3 AlgClosedQ).FunctionField
              ((φ (Multiplicative.ofAdd P) : AlgClosedQˣ) : AlgClosedQ)
            = weilPairingPointElt g (P : (y2AddYEqX3 AlgClosedQ).Point) := by
  classical
  obtain ⟨xS, yS, hS, hmS⟩ :=
    exists_nonsingular_mem_torsion (W := y2AddYEqX3 AlgClosedQ) (n := 5)
      (by norm_num) (by norm_num) (by norm_num)
  exact ⟨xS, yS, hS,
    exists_weilPairingTorsionMuHom_n_ne_one (by norm_num) (by norm_num) hS hmS⟩

end Nonvacuity

end WeierstrassCurve.Affine
