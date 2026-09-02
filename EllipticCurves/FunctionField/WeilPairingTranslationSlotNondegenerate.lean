/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.WeilPairingNondegenerateMu
import EllipticCurves.FunctionField.WeilPairingTranslationSlotHom

/-!
# Non-degeneracy of `e_n(S, ·)` as a statement about the *map* (rung 6)

`EllipticCurves.FunctionField.WeilPairingTranslationSlotHom` (`#890`) bundles the translation slot
of the Weil pairing into a homomorphism of groups,

```lean
weilPairingTorsionMuHom_two h2 hgS hu : Multiplicative (W.torsion 2) →* rootsOfUnity 2 F,
```

and `EllipticCurves.FunctionField.WeilPairingNondegenerateMu` (`#878`) opens by saying what the
whole `μ_n(F)` layer is *for*:

> The statement non-degeneracy is *for* is that the homomorphism `e_n(S, ·) : E[n] → μ_n(F)` is not
> trivial […] the form that will compose with a bundled pairing **when one exists**.

One exists.  This file says it is not trivial: `weilPairingTorsionMuHom_{two,three} ≠ 1`, its
kernel is a proper subgroup, and the Silverman III.8.1(d) converse `e_n(S, ·) ≡ 1 → S = O` becomes
a statement about a single equation of homomorphisms.  **Nothing new is proved here about curves**
— every input is a merged headline of `WeilPairingNondegenerateMu`, exactly as that file was a
restatement of `#791`/`#831` one level down.

## ⚠️ The transfer to the `Point` layer is `rfl`, and a reader will expect otherwise

`weilPairingPointMu` (`Point`-indexed) and `weilPairingMu` (`Equation`-indexed) are
`Classical.choose` of **different** existence proofs — `weilPairingPointElt_isRootOfUnity` and
`weilPairingElt_isRootOfUnity` — so the expected route from one to the other is a descent through
`algebraMap_coe_rootsOfUnity_injective` (`#459`) using the two `algebraMap_coe_` rules.  **That
descent is not needed.**  `weilPairingPointElt_isRootOfUnity` is proved by cases on the point and
its affine branch is literally `weilPairingElt_isRootOfUnity h.left hn hpow`, which reduces on the
`Point.some` constructor; the two `Classical.choose` terms are therefore the *same* term, and
proof-irrelevance in `hpow` absorbs the mismatched datum.  So `weilPairingPointMu_some` is `rfl`,
and with it the two `weilPairingTorsionMuHom_*_apply_some` value rules, which are what every proof
below goes through.

This is the same phenomenon `#890` recorded for `map_mul'`: once the datum is a `Prop`, the
`Point` layer and the `Equation` layer are definitionally the same object wherever both are
defined.

## ⚠️ Where the bundling changes the statement rather than restating it

`eq_zero_of_forall_weilPairingMu_eq_one_two`'s trivial-pairing hypothesis is a `∀` over `x₂ y₂ h₂`,
over torsion membership, **and over `hpow`** — four binders, the last of which
`WeilPairingNondegenerateMu` has to spend a docstring section explaining ("the extra binder is type
theory, not mathematics").  In `eq_zero_of_weilPairingTorsionMuHom_two_eq_one` that entire
hypothesis is the single equation `φ = 1`.  That is III.8.1(d) in the shape a reader expects, and
the apology for the binder is no longer needed.

The `≠ 1` headlines are the mirror move on the other side: "some affine `T ∈ E[n]` has
`e_n(S, T) ≠ 1`" becomes "the map is not the trivial homomorphism", with the witness quantified
away.

## Main results

* `weilPairingPointMu_some`, `weilPairingTorsionMuHom_{two,three}_apply_some` — the `rfl` bridges,
  ungated, and the only thing in this file that is not a two-line corollary;
* `weilPairingTorsionMuHom_{two,three}_ne_one` — **the map is not trivial**;
* `ker_weilPairingTorsionMuHom_{two,three}_ne_top` — its kernel is a proper subgroup;
* `eq_zero_of_weilPairingTorsionMuHom_{two,three}_eq_one` — Silverman III.8.1(d): if the map is
  trivial then `S = O`;
* `exists_weilPairingTorsionMuHom_{two,three}_ne_one` — over `F̄`, with no hypothesis beyond the
  setting: `e_n(S, ·) : E[n] → μ_n(F)` **is a non-trivial group homomorphism** at `n = 2, 3`.

## Scope

`[Field F] {W : Affine F} [W.IsElliptic]`.  The three bridge lemmas are ungated.  Everything else
inherits `[IsAlgClosed F]` from the `WeilPairingNondegenerateMu` envelopes and **from nowhere
else** — the single source is `hprin`, i.e. `exists_gS_{two,three}_of_isAlgClosed` (`#791`/`#825`),
as for every other `[IsAlgClosed F]` on this front.  No hypothesis is added to any envelope: only
the conclusions move.

Out of scope: combining the two slots into a pairing on `W.Point × W.Point` (`#873`/`#890` both
record that as a separate design question and it stays one); general `n` (`#251`); `hprin`
over a general field, open at both `n`.  Nothing existing is renamed or reproved: this module is
purely additive.

⚠️ **That bullet used to read *"general `n` (`#404`'s `ωₙ`)"*, and `#404` is closed.**  PR #557
proved the on-curve identity for `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` at every index over every commutative ring —
`WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero`, `EllipticCurves.Torsion.OmegaCrux`.  What still
gates a general index here is the *other* statement this tree also called `ωₙ`: the identification
of those coordinates with the **group-law** multiple `n • P`, which is `#251`.  That is the step
`hprin` reaches through `MulByTwoFibreAffine`/`MulByThreeFibre`, whose own input is
`addY_self_eq_div` (`EllipticCurves.Torsion.DoublingCoords`) and its `n = 3` mirror.  ⚠️ The
two-reading account is `EllipticCurves.FunctionField.MulByNPullback`.

⚠️ **That list used to open** *"**injectivity** of the map, which is a different statement and is
Ward/`#242`-gated through `#E[n] = n²`"*.  It was right that injectivity is a different statement
and wrong about everything else: **injectivity of `e_n(S, ·)` is not open, it is false**, and the
theorem named as the gate is the theorem that refutes it.  `#E[n] = n²` over `F̄` is merged at both
`n` (`card_torsion_two`, `card_torsion_three`), `#μ_n(F̄) = n` is merged
(`natCard_rootsOfUnity_of_ne_zero`), and `n² > n`, so no injection exists.  The refutation is
`not_injective_weilPairingTorsionMuHom_{two,three}`
(`EllipticCurves.FunctionField.WeilPairingTranslationSlotNotInjective`), with
`ker_weilPairingTorsionMuHom_{two,three}_ne_bot` beside the `ker_…_ne_top` family proved here.

⚠️ **Nothing about this front is weaker than the clause suggested; the clause credited a false
statement with being merely open.**  What non-degeneracy asserts about the map is `≠ 1`, which is
what this file proves and is sharp — on the canonical root and for `S ≠ O` the same slot is even
*onto* `μ_n(F̄)` (`weilPairingTwo_surjective`,
`EllipticCurves.FunctionField.WeilPairingSurjective`, `#938`).  And
the statement that *is* injective, and in fact bijective, is the **other** slot `S ↦ e_n(S, ·)`
into the dual group: `bijective_weilPairingTwoHom`
(`EllipticCurves.FunctionField.WeilPairingPerfect`, `#940`).  The conceptual reason a fixed slot
cannot be injective is `e_n(S, S) = 1`, which puts `⟨S⟩` in the kernel whenever `S` is an
`F`-rational point of order `n`; this tree proves that identity only in an `∃`-shape that produces
its own root, so `not_injective_weilPairingTorsionMuHom_{two,three}` is the counting refutation
instead — and it is the counting argument, not the group-theoretic one, that `[IsAlgClosed F]` is
load-bearing for.

⚠️ **This clause was born after the sweep that should have made it unwritable, and no sweep could
have caught it.**

| | commit | time |
|---|---|---|
| `card_torsion_two` (`#E[2] = 4`), the theorem named as the gate | `7089d8d` | 08-19 21:23:26 |
| `#769` retires *"non-degeneracy is Ward-gated"*, eighteen files | `1969c65` | 08-22 22:14:20 |
| `#785` audits the `#769` pointer sites, finds a nineteenth copy | `1792fba` | 08-23 00:56:50 |
| `weilPairingTorsionMuHom_two` is defined | `f167fbc` | 08-23 15:08:54 |
| **this file is created, carrying the clause** | `42d6afa` | 08-23 **15:47:52** |

(All 2026.)

Fourteen hours and fifty-one minutes after the audit closed, and thirty-nine minutes after the map
itself existed, a **twentieth** instance of the retired sentence shape — *"`X` is Ward/`#242`-gated
through `#E[n] = n²`"* — entered a file neither sweep could have read.  ⚠️ **A retirement sweep
does not inoculate the tree against the same sentence being written again the next day**, and
re-running `#769`'s grep would not have found this one either: it was
keyed on *non-degeneracy*, and this clause hangs the same gate on *injectivity* — a neighbouring
statement, one word apart, and the one where `#242` at `n = 2` is not a discharged gate but a
refutation.

## Placement

The lemma layer — the `Point`/`Equation` bridge and the `weilPairingTorsionMuHom_*_ne_one`,
`ker_…_ne_top` and `eq_zero_of_…` families, all of which take the root and its rung-5 certificate as
hypotheses — lives in `WeierstrassCurve.Affine.CoordinateRing`.  The two `exists_` headlines over
`F̄` live one level up in `WeierstrassCurve.Affine`, reached with `open CoordinateRing`; that is
`#903`'s house pattern.

⚠️ **`#918` moved those two up, together with `#873`'s pair in
`EllipticCurves.FunctionField.WeilPairingTranslationSlotHom`.**  Only `#873`'s pair had an
arbitrary-field twin whose namespace disagreed, but moving it alone would have split
`exists_weilPairingTorsionMuHom_two` from `exists_weilPairingTorsionMuHom_two_ne_one` — the same
defect one name over.  **A namespace fix that leaves a sibling behind has relocated the problem, not
solved it.**  Nothing here changed but the prefix: no statement, no proof, no binder.

## Non-vacuity

Both `exists_` headlines are instantiated below on the curves `#845`/`#861`/`#873`/`#890` use —
`y² = x³ − x` over `AlgebraicClosure ℚ` with `S = (0, 0) ∈ E[2]`, and `y² + y = x³` with
`S = (0, 0) ∈ E[3]`.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(a), III.8.1(d).
-/

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic] {x y : F}

/-! ### The bridge from the `Point` layer to the `Equation` layer -/

open Classical in
/-- **The `Point`-indexed value at an affine point is the `Equation`-indexed one**, definitionally.

⚠️ `weilPairingPointMu` and `weilPairingMu` are `Classical.choose` of two *different* existence
proofs, so the expected proof is a descent through `algebraMap_coe_rootsOfUnity_injective` using
the two `algebraMap_coe_` rules.  It is not needed: the affine branch of
`weilPairingPointElt_isRootOfUnity` **is** `weilPairingElt_isRootOfUnity`, and it reduces on the
`Point.some` constructor, so the two chosen terms are the same term.  The two `hpow` arguments may
differ; `weilPairingPointMu` is proof-irrelevant in that slot. -/
theorem weilPairingPointMu_some {g : W.FunctionField} (hg : g ≠ 0) {n : ℕ} [NeZero n]
    (h : W.Nonsingular x y) (hpow : weilPairingPointElt g (.some x y h) ^ n = 1)
    (hpow' : weilPairingElt h.left g ^ n = 1) :
    weilPairingPointMu hg hpow = weilPairingMu h.left hpow' :=
  rfl

open Classical in
/-- **The value of the bundled `n = 2` map at an affine torsion point** is the merged
`weilPairingMu`.  `rfl`, by `weilPairingPointMu_some`; this is what lets the pointwise
non-degeneracy headlines be read as statements about the map.

⚠️ Not a `simp` lemma: `hpow` appears on the right and not on the left. -/
theorem weilPairingTorsionMuHom_two_apply_some (h2 : (2 : F) ≠ 0) {f gS : W.FunctionField}
    {u : W.CoordinateRingˣ} (hgS : gS ≠ 0)
    (hu : (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f)
    (h₂ : W.Nonsingular x y) (hmem : Point.some x y h₂ ∈ W.torsion 2)
    (hpow : weilPairingElt h₂.left gS ^ 2 = 1) :
    weilPairingTorsionMuHom_two h2 hgS hu
        (Multiplicative.ofAdd (⟨Point.some x y h₂, hmem⟩ : W.torsion 2))
      = weilPairingMu h₂.left hpow :=
  rfl

open Classical in
/-- **The value of the bundled `n = 3` map at an affine torsion point**, the mirror of
`weilPairingTorsionMuHom_two_apply_some` and equally `rfl`. -/
theorem weilPairingTorsionMuHom_three_apply_some (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {f gS : W.FunctionField} {u : W.CoordinateRingˣ} (hgS : gS ≠ 0)
    (hu : (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f)
    (h₃ : W.Nonsingular x y) (hmem : Point.some x y h₃ ∈ W.torsion 3)
    (hpow : weilPairingElt h₃.left gS ^ 3 = 1) :
    weilPairingTorsionMuHom_three h2 h3 hgS hu
        (Multiplicative.ofAdd (⟨Point.some x y h₃, hmem⟩ : W.torsion 3))
      = weilPairingMu h₃.left hpow :=
  rfl

section IsAlgClosed

variable [IsAlgClosed F]

/-! ### `n = 2` -/

open Classical in
/-- **The bundled pairing map is not the trivial homomorphism**, at `n = 2`.

```
e_2(S, ·) : E[2] → μ_2(F) is not 1.
```

The envelope is `exists_torsion_two_weilPairingMu_ne_one`'s, **unchanged**: same principal `f_S`
with `div f_S = 2·(S)`, same rung-5 certificate `hu`.  Only the conclusion moves — the affine
witness `T` that file exhibits is quantified away, and what is left is a statement about the map. -/
theorem weilPairingTorsionMuHom_two_ne_one (h2 : (2 : F) ≠ 0) (h : W.Nonsingular x y)
    {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ))
    (hgS : gS ≠ 0) {u : W.CoordinateRingˣ}
    (hu : (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f) :
    weilPairingTorsionMuHom_two h2 hgS hu ≠ 1 := by
  obtain ⟨x₂, y₂, h₂, hmem, hpow, hne⟩ :=
    exists_torsion_two_weilPairingMu_ne_one h2 h hf hfdiv hgS hu
  refine fun hone => hne ?_
  have hval := DFunLike.congr_fun hone
    (Multiplicative.ofAdd (⟨Point.some x₂ y₂ h₂, hmem⟩ : W.torsion 2))
  rwa [weilPairingTorsionMuHom_two_apply_some h2 hgS hu h₂ hmem hpow] at hval

open Classical in
/-- **The kernel of the bundled map is a proper subgroup of `E[2]`**: some `2`-torsion point does
not pair trivially with `S`.  The `MonoidHom.ker` form of
`weilPairingTorsionMuHom_two_ne_one`. -/
theorem ker_weilPairingTorsionMuHom_two_ne_top (h2 : (2 : F) ≠ 0) (h : W.Nonsingular x y)
    {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ))
    (hgS : gS ≠ 0) {u : W.CoordinateRingˣ}
    (hu : (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f) :
    MonoidHom.ker (weilPairingTorsionMuHom_two h2 hgS hu) ≠ ⊤ := by
  obtain ⟨x₂, y₂, h₂, hmem, hpow, hne⟩ :=
    exists_torsion_two_weilPairingMu_ne_one h2 h hf hfdiv hgS hu
  refine fun htop => hne ?_
  have hval : (Multiplicative.ofAdd (⟨Point.some x₂ y₂ h₂, hmem⟩ : W.torsion 2))
      ∈ MonoidHom.ker (weilPairingTorsionMuHom_two h2 hgS hu) := htop ▸ Subgroup.mem_top _
  rw [MonoidHom.mem_ker, weilPairingTorsionMuHom_two_apply_some h2 hgS hu h₂ hmem hpow] at hval
  exact hval

open Classical in
/-- **Silverman III.8.1(d) at `n = 2`, as a statement about the map**: if `e_2(S, ·)` is the
trivial homomorphism then `S = O`.

⚠️ Compare `eq_zero_of_forall_weilPairingMu_eq_one_two`, whose trivial-pairing hypothesis is a `∀`
over `x₂ y₂ h₂`, over torsion membership **and over `hpow`**.  Here it is the single equation `φ =
1`. That is the whole gain from bundling, and it is why the binder apology in
`WeilPairingNondegenerateMu`'s docstring does not have to be repeated. -/
theorem eq_zero_of_weilPairingTorsionMuHom_two_eq_one (h2 : (2 : F) ≠ 0) {S : W.Point}
    {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = (2 : ℤ) • pointDivisorAff W S) (hgS : gS ≠ 0)
    {u : W.CoordinateRingˣ} (hu : (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f)
    (hone : weilPairingTorsionMuHom_two h2 hgS hu = 1) :
    S = 0 := by
  refine eq_zero_of_forall_weilPairingMu_eq_one_two h2 hf hfdiv hgS hu fun x₂ y₂ h₂ hmem hpow => ?_
  have hval := DFunLike.congr_fun hone
    (Multiplicative.ofAdd (⟨Point.some x₂ y₂ h₂, hmem⟩ : W.torsion 2))
  rwa [weilPairingTorsionMuHom_two_apply_some h2 hgS hu h₂ hmem hpow] at hval

/-! ### `n = 3` -/

open Classical in
/-- **The bundled pairing map is not the trivial homomorphism**, at `n = 3`.  The mirror of
`weilPairingTorsionMuHom_two_ne_one`, off `exists_torsion_three_weilPairingMu_ne_one`. -/
theorem weilPairingTorsionMuHom_three_ne_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h : W.Nonsingular x y) {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ))
    (hgS : gS ≠ 0) {u : W.CoordinateRingˣ}
    (hu : (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f) :
    weilPairingTorsionMuHom_three h2 h3 hgS hu ≠ 1 := by
  obtain ⟨x₃, y₃, h₃, hmem, hpow, hne⟩ :=
    exists_torsion_three_weilPairingMu_ne_one h2 h3 h hf hfdiv hgS hu
  refine fun hone => hne ?_
  have hval := DFunLike.congr_fun hone
    (Multiplicative.ofAdd (⟨Point.some x₃ y₃ h₃, hmem⟩ : W.torsion 3))
  rwa [weilPairingTorsionMuHom_three_apply_some h2 h3 hgS hu h₃ hmem hpow] at hval

open Classical in
/-- **The kernel of the bundled map is a proper subgroup of `E[3]`.**  The `n = 3` mirror of
`ker_weilPairingTorsionMuHom_two_ne_top`. -/
theorem ker_weilPairingTorsionMuHom_three_ne_top (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h : W.Nonsingular x y) {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ))
    (hgS : gS ≠ 0) {u : W.CoordinateRingˣ}
    (hu : (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f) :
    MonoidHom.ker (weilPairingTorsionMuHom_three h2 h3 hgS hu) ≠ ⊤ := by
  obtain ⟨x₃, y₃, h₃, hmem, hpow, hne⟩ :=
    exists_torsion_three_weilPairingMu_ne_one h2 h3 h hf hfdiv hgS hu
  refine fun htop => hne ?_
  have hval : (Multiplicative.ofAdd (⟨Point.some x₃ y₃ h₃, hmem⟩ : W.torsion 3))
      ∈ MonoidHom.ker (weilPairingTorsionMuHom_three h2 h3 hgS hu) := htop ▸ Subgroup.mem_top _
  rw [MonoidHom.mem_ker,
    weilPairingTorsionMuHom_three_apply_some h2 h3 hgS hu h₃ hmem hpow] at hval
  exact hval

open Classical in
/-- **Silverman III.8.1(d) at `n = 3`, as a statement about the map.**  The mirror of
`eq_zero_of_weilPairingTorsionMuHom_two_eq_one`; `S : W.Point` is arbitrary and the divisor
condition is written with `pointDivisorAff`, which is `n`-free and sends `O` to `0`, so no case
split appears in the statement. -/
theorem eq_zero_of_weilPairingTorsionMuHom_three_eq_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {S : W.Point} {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = (3 : ℤ) • pointDivisorAff W S) (hgS : gS ≠ 0)
    {u : W.CoordinateRingˣ} (hu : (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f)
    (hone : weilPairingTorsionMuHom_three h2 h3 hgS hu = 1) :
    S = 0 := by
  refine eq_zero_of_forall_weilPairingMu_eq_one_three h2 h3 hf hfdiv hgS hu
    fun x₃ y₃ h₃ hmem hpow => ?_
  have hval := DFunLike.congr_fun hone
    (Multiplicative.ofAdd (⟨Point.some x₃ y₃ h₃, hmem⟩ : W.torsion 3))
  rwa [weilPairingTorsionMuHom_three_apply_some h2 h3 hgS hu h₃ hmem hpow] at hval

end IsAlgClosed

end CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

open CoordinateRing

section IsAlgClosed

variable [IsAlgClosed F]

/-! ### Over `F̄`, with no hypothesis beyond the setting -/

open Classical in
/-- **`e_2(S, ·) : E[2] → μ_2(F̄)` is a *non-trivial* group homomorphism, unconditionally.**

The shape `exists_weilPairingTorsionMuHom_two` (`#890`) returns, with the `φ ≠ 1` conjunct added,
so the two compose rather than diverge: the rung-5 certificate is produced by
`exists_gS_two_of_isAlgClosed` (`#791`), which is the only place `[IsAlgClosed F]` enters. -/
theorem exists_weilPairingTorsionMuHom_two_ne_one (h2 : (2 : F) ≠ 0) {xS yS : F}
    (hS : W.Nonsingular xS yS) (hmS : Point.some xS yS hS ∈ W.torsion 2) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
      ∃ φ : Multiplicative (W.torsion 2) →* rootsOfUnity 2 F, φ ≠ 1 ∧
        ∀ P : W.torsion 2,
          algebraMap F W.FunctionField ((φ (Multiplicative.ofAdd P) : Fˣ) : F)
            = weilPairingPointElt g (P : W.Point) := by
  obtain ⟨f, hf, hd, g, hg, u, hu⟩ := exists_gS_two_of_isAlgClosed h2 hS hmS
  exact ⟨g, hg, ⟨f, hf, hd, u, hu⟩, weilPairingTorsionMuHom_two h2 hg hu,
    weilPairingTorsionMuHom_two_ne_one h2 hS hf hd hg hu,
    fun P => algebraMap_coe_weilPairingTorsionMuHom_two h2 hg hu P⟩

open Classical in
/-- **`e_3(S, ·) : E[3] → μ_3(F̄)` is a *non-trivial* group homomorphism, unconditionally.**  The
`n = 3` mirror, off `exists_gS_three_of_isAlgClosed` (`#825`). -/
theorem exists_weilPairingTorsionMuHom_three_ne_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xS yS : F} (hS : W.Nonsingular xS yS) (hmS : Point.some xS yS hS ∈ W.torsion 3) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) ∧
      ∃ φ : Multiplicative (W.torsion 3) →* rootsOfUnity 3 F, φ ≠ 1 ∧
        ∀ P : W.torsion 3,
          algebraMap F W.FunctionField ((φ (Multiplicative.ofAdd P) : Fˣ) : F)
            = weilPairingPointElt g (P : W.Point) := by
  obtain ⟨f, hf, hd, g, hg, u, hu⟩ := exists_gS_three_of_isAlgClosed h2 h3 hS hmS
  exact ⟨g, hg, ⟨f, hf, hd, u, hu⟩, weilPairingTorsionMuHom_three h2 h3 hg hu,
    weilPairingTorsionMuHom_three_ne_one h2 h3 hS hf hd hg hu,
    fun P => algebraMap_coe_weilPairingTorsionMuHom_three h2 h3 hg hu P⟩

end IsAlgClosed

/-! ### Non-vacuity

Both `exists_` headlines are certified below on the curves `#845`/`#861`/`#873`/`#890` use.  What
each produces on a curve that exists, with nothing left over: a rung-5 root `g` at `S`, a group
homomorphism `E[n] → μ_n(F̄)` computing `e_n(S, ·)`, and the statement that it is **not** the
trivial homomorphism. -/

section Nonvacuity

/-! The certificate curves `y² = x³ − x` and `y² + y = x³` are the shared
`EllipticCurves.Fixture.y2EqX3SubX` and `EllipticCurves.Fixture.y2AddYEqX3`, and the base —
algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here. -/

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

private lemma exampleNsS : (y2EqX3SubX AlgClosedQ).Nonsingular 0 0 :=
  (y2EqX3SubX AlgClosedQ).equation_iff_nonsingular.mp (by
    norm_num [y2EqX3SubX, WeierstrassCurve.Affine.equation_iff])

open Classical in
private lemma exampleTorS :
    Point.some (0 : AlgClosedQ) 0 exampleNsS ∈ (y2EqX3SubX AlgClosedQ).torsion 2 :=
  (mem_torsion_two_some_iff exampleNsS).mpr (by norm_num [y2EqX3SubX])

open Classical in
/-- **`e_2(S, ·) : E[2] → μ_2(F̄)` is a non-trivial group homomorphism, on a curve that exists.**
`S = (0, 0)` on `y² = x³ − x`; no hypothesis survives. -/
example : ∃ (g : (y2EqX3SubX AlgClosedQ).FunctionField)
    (φ : Multiplicative ((y2EqX3SubX AlgClosedQ).torsion 2) →* rootsOfUnity 2 AlgClosedQ), φ ≠ 1 ∧
    ∀ P : (y2EqX3SubX AlgClosedQ).torsion 2,
      algebraMap AlgClosedQ (y2EqX3SubX AlgClosedQ).FunctionField
          ((φ (Multiplicative.ofAdd P) : AlgClosedQˣ) : AlgClosedQ)
        = weilPairingPointElt g (P : (y2EqX3SubX AlgClosedQ).Point) := by
  obtain ⟨g, -, -, φ, hφ, hval⟩ :=
    exists_weilPairingTorsionMuHom_two_ne_one exampleTwo exampleNsS exampleTorS
  exact ⟨g, φ, hφ, hval⟩

private lemma exampleNsThreeS : (y2AddYEqX3 AlgClosedQ).Nonsingular 0 0 :=
  (y2AddYEqX3 AlgClosedQ).equation_iff_nonsingular.mp (by
    norm_num [y2AddYEqX3, WeierstrassCurve.Affine.equation_iff])

open Classical in
private lemma exampleTorThreeS :
    Point.some (0 : AlgClosedQ) 0 exampleNsThreeS ∈ (y2AddYEqX3 AlgClosedQ).torsion 3 :=
  mem_torsion_three_some_iff'.mpr (by
    norm_num [y2AddYEqX3, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈])

open Classical in
/-- **`e_3(S, ·) : E[3] → μ_3(F̄)` is a non-trivial group homomorphism, on a curve that exists.**
`S = (0, 0)` on `y² + y = x³`.  ⚠️ Only the *divisor* point has to be nameable: the translation
slot is quantified as a group, so `#873`'s limitation — no second `3`-torsion point of this curve
is nameable — does not bite, exactly as in `#890`. -/
example : ∃ (g : (y2AddYEqX3 AlgClosedQ).FunctionField)
    (φ : Multiplicative ((y2AddYEqX3 AlgClosedQ).torsion 3) →* rootsOfUnity 3 AlgClosedQ), φ ≠ 1 ∧
    ∀ P : (y2AddYEqX3 AlgClosedQ).torsion 3,
      algebraMap AlgClosedQ (y2AddYEqX3 AlgClosedQ).FunctionField
          ((φ (Multiplicative.ofAdd P) : AlgClosedQˣ) : AlgClosedQ)
        = weilPairingPointElt g (P : (y2AddYEqX3 AlgClosedQ).Point) := by
  obtain ⟨g, -, -, φ, hφ, hval⟩ := exists_weilPairingTorsionMuHom_three_ne_one exampleTwo
    exampleThree exampleNsThreeS exampleTorThreeS
  exact ⟨g, φ, hφ, hval⟩

end Nonvacuity

end WeierstrassCurve.Affine
