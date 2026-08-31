/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairingNondegenerateThree
import EllipticCurves.FunctionField.WeilPairingNondegenerateTwo
import EllipticCurves.FunctionField.WeilPairingRootsOfUnity

/-!
# Non-degeneracy of the Weil pairing in `μ_n(F)`, unconditionally over `F̄` (rung 6)

`EllipticCurves.FunctionField.WeilPairingNondegenerateTwo` (`#796`) and
`EllipticCurves.FunctionField.WeilPairingNondegenerateThree` (`#831`) prove non-degeneracy as an
inequation in the function field: some affine `T ∈ E[n]` has `e_n(S, T) ≠ 1` in `F(W)`.  This file
restates all six of their headlines as inequations in the group `rootsOfUnity n F`, at `n = 2` and
`n = 3`.  **Nothing new is proved here about curves.**

## Why the `μ_n(F)` form is the one non-degeneracy wants

`weilPairingElt h₂ g ≠ 1` says that a particular rational function is not the constant `1`.  The
statement non-degeneracy is *for* is that the homomorphism `e_n(S, ·) : E[n] → μ_n(F)` is not
trivial, and that is an inequation in `μ_n(F)` — the form that will compose with a bundled pairing
when one exists.  Every other rung-6 headline on this front is stated at both levels; before this
file, non-degeneracy was the one slot stated only in `F(W)`.

## The route: one descent lemma, applied six times

`weilPairingMu_eq_one_iff` (`WeilPairingRootsOfUnity`, `#733`; ⚠️ it was in
`WeilPairingAntisymmetricMu` when this file was written and `#883` moved it next to the definition
it is about, which drops four modules from this file's transitive imports —
`WeilPairingAntisymmetric`, `WeilPairingAntisymmetricMu`, `WeilPairingBilinearBaseField` and
`WeilPairingBilinearMu`) is
`weilPairingMu h₂ hpow = 1 ↔ weilPairingElt h₂ g = 1`, for arbitrary `n` and with no `g ≠ 0`
hypothesis.  Each theorem below is its `.not` applied to the corresponding `F(W)` headline, so the
mathematical content is entirely upstream and the only work is producing the `hpow` datum.

⚠️ That figure is **this file's** cone before and after, which is the only honest way to price such
a move: the cone of the import that was dropped (`WeilPairingAntisymmetricMu`, 31) is an upper
bound, and here it overstates the saving eightfold, because `WeilPairingNondegenerateTwo` and
`...Three` already supply all but those four.  `#887` corrected this passage, which had claimed
`50`.

That datum is **produced, not assumed**.  The non-degeneracy envelopes already carry the rung-5
certificate `hu : u · g_S ^ n = [n]∗ f_S` and return the witness with its torsion membership, which
is exactly what the two producers need:

* `n = 2`: `weilPairingElt_pow_eq_one_of_gS_two_torsion` (`TranslationTorsion`);
* `n = 3`: `weilPairingElt_pow_eq_one_of_gS_three_baseField` (`TranslationTriplingComm`).

Both are polymorphic in the exponent of `g_S`, so neither needs the pairing value to be a constant
of `F` first.

## ⚠️ Why `hpow` is bound in the statement, and why that is not a hypothesis

`weilPairingMu` is *indexed by the proof* `hpow : e_n(S, T) ^ n = 1` — one cannot write
`weilPairingMu h₂.left hpow` without producing `hpow`.  So the conclusions below read
`∃ hpow : weilPairingElt h₂.left g_S ^ n = 1, weilPairingMu h₂.left hpow ≠ 1` rather than a bare
inequation.  **The extra binder is type theory, not mathematics**: the `F(W)`-level headlines assume
nothing that these do not, and `hpow` is discharged from data the envelope already carries.  This is
the same shape, and the same reason, as `#873`'s `μ_n(F)` bilinearity headlines.

⚠️ Dually, the Silverman-shaped theorems quantify their trivial-pairing hypothesis over `hpow`:
`∀ hpow, weilPairingMu h₂.left hpow = 1`.  A reader may wonder whether that is a *stronger*
hypothesis than naming one `hpow`.  It is not: `hpow` proves a `Prop`, so all its inhabitants are
definitionally equal, and the `∀` form is chosen only so that a caller need not name a proof term it
has no reason to have.

## Main statements

At each of `n = 2` and `n = 3`, mirroring the three headlines of the corresponding `F(W)` file:

* `WeierstrassCurve.Affine.exists_torsion_two_weilPairingMu_ne_one` and
  `WeierstrassCurve.Affine.exists_torsion_three_weilPairingMu_ne_one` — the carried form: against an
  arbitrary rung-5 root, some affine `T ∈ E[n]` has `e_n(S, T) ≠ 1` in `μ_n(F)`.
* **`WeierstrassCurve.Affine.exists_gS_two_weilPairingMu_ne_one`** and
  **`WeierstrassCurve.Affine.exists_gS_three_weilPairingMu_ne_one`** — the headlines: rung 5 and
  non-degeneracy together, with no hypothesis beyond the setting and a nonsingular affine
  `n`-torsion point.
* `WeierstrassCurve.Affine.eq_zero_of_forall_weilPairingMu_eq_one_two` and
  `WeierstrassCurve.Affine.eq_zero_of_forall_weilPairingMu_eq_one_three` — Silverman III.8.1(d) in
  `μ_n(F)`: `e_n(S, ·) ≡ 1` on `E[n]` forces `S = O`.

⚠️ **The witness `T` is necessarily affine**, for the reason both `F(W)` files record: at `T = O`
the translation is the identity and `e_n(S, O) = 1` trivially, so every conclusion below names `T`
by giving its coordinates.

## Scope

Out of scope, and untouched: `hprin` over a **general** field, which is what confines all of this
to `F̄` at both `n`; general `n` (see below); bundling into `weilPairingMuHom`, which needs a
`hpow` datum uniform in the slot variable and is a separate design question
(`WeilPairingDivisorSlotHom` states the obstruction); any change to the six `F(W)`-level theorems or
their proofs.

⚠️ **The general-`n` entry above used to carry a reason, and the reason was wrong** — it read
*"general `n` (`#404`'s `ωₙ`)"*.  `[n]∗` needs no `y`-coordinate division polynomial (`#1165`), and
the rung-5 root and the whole rung-6 translation slot are now stated at every `n`, with the
non-constancy side condition discharged at every `3`-smooth `n` (`#1304`, `#1308`).  What confines
the headlines above to `n = 2, 3` is the **same** `hprin` the previous clause already names: its
only producers over `F̄` are `exists_gS_{two,three}_of_isAlgClosed` (`#791`/`#825`), whose input is
the fibre description `[n]∗((S) − (O)) = ∑_{R ∈ E[n]} ((P ⊕ R) − (R))`, merged only at `n = 2`
(`MulByTwoFibreAffine`) and `n = 3` (`MulByThreeFibre`).  ⚠️ So the two entries are one gate read
along two axes, not two gates, and `#404` is not on this file's path at all.

⚠️ **This is not a perfect-pairing statement, but one exists.**  Non-degeneracy in one slot is
what Silverman III.8.1(d) asserts and what is proved here.  Perfectness is
`bijective_weilPairing{Two,Three}Hom`, bundled as `weilPairing{Two,Three}Equiv`
(`EllipticCurves.FunctionField.WeilPairingPerfect`, `#940`): the bundled map
`Multiplicative E[n] →* (Multiplicative E[n] →* μ_n(F̄))` is **bijective**, so `E[n]` is its own
dual.  Nothing here narrows the distance to it — that remains true — but this file's six headlines
are not the input either; `#940` runs off `ker_weilPairing{Two,Three}Hom` and
`Mathlib.GroupTheory.FiniteAbelian.Duality`.

⚠️ **The reason this bullet gave was wrong as well as its conclusion.**  It read *"A statement that
`e_n` is a perfect pairing on `E[n] × E[n]` would want a pairing defined on `W.Point × W.Point`;
there is none in this tree, since `weilPairingElt` takes a *function*"*.  A perfect-pairing
statement wants a pairing on `E[n]`, and it is `EllipticCurves.FunctionField.WeilPairingFunctionTwo`
(`#922`) that supplies one — whose own scope section says the pairing **has to be** a function of
`E[2] × E[2]` and not of `W.Point × W.Point`, because the rung-5 root exists only at torsion points.
So the missing object was never the one this bullet named, and naming the wrong obstruction is what
made the statement look further away than it was.

⚠️ **The statements below are pinned to `Classical.propDecidable`**, as the two `F(W)` files are:
`open Classical in` is required, not decorative, because `TorsionTwoMul` / `TorsionThreeMul` bake
the classical `DecidableEq F` instance in and the statements mention `W.torsion n`.

## Non-vacuity

Each headline is certified below on the certificate curve of its own `n`.  ⚠️ **Two curves are
needed and that is intrinsic, not stylistic.**  `y² = x³ − x` serves at `n = 2` with the torsion
point named as `(0, 0)`, but its `Ψ₃ = 3X⁴ − 6X² − 1` has no rational root, so none of its nine
`3`-torsion points can be named without a genuine algebraic-number argument; `n = 3` uses
`y² + y = x³`, where `Ψ₃ = 3X(X³ + 1)` vanishes at `0`.  This is the `n = 3` file's warning and it
transposes without change.

⚠️ The certificate scaffolding is **duplicated** from the two `F(W)` files rather than imported:
theirs is `private`, so it is not visible here, and de-`private`-ing it would edit two files this
one otherwise does not touch.  `#855` set that precedent.

## ⚠️ `WeilPairingNondegenerateTwo` was cited as `#791`; it is `#796`

Corrected in place, not retired.  Its creation commit subject ends *"non-degeneracy of the Weil
pairing at `n = 2` over an algebraically closed field (#796) (#323)"*; `#791` is
`exists_gS_two_of_isAlgClosed`'s issue, which this file also cites — correctly — in the docstring
of `exists_gS_two_weilPairingMu_ne_one`.

⚠️ Note that the *same sentence* cites `WeilPairingNondegenerateThree` as `#831`, which is
**right**.  So this was not a file-wide copy of one bad number but a single slip inside an
otherwise correct sentence — a different generating mechanism from a systematic shift, and the
reason "check the file once and move on" is not a sound strategy either way round.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8, Prop. 8.1(d).
-/

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

section Nondegenerate

variable [W.IsElliptic] [IsAlgClosed F] {x y : F}

/-! ### `n = 2` -/

open Classical in
/-- **Non-degeneracy at `n = 2` in `μ_2(F)`, against an arbitrary rung-5 root**: some affine
`T ∈ E[2]` has `e_2(S, T) ≠ 1` as an element of `rootsOfUnity 2 F`.

The envelope is `exists_torsion_two_weilPairingElt_ne_one`'s, unchanged.  The `hpow` datum is
produced from the rung-5 certificate `hu` that envelope already carries, by
`weilPairingElt_pow_eq_one_of_gS_two_torsion`, and the inequation is transported by
`weilPairingMu_eq_one_iff`. -/
theorem exists_torsion_two_weilPairingMu_ne_one (h2 : (2 : F) ≠ 0) (h : W.Nonsingular x y)
    {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ))
    (hgS : gS ≠ 0) {u : W.CoordinateRingˣ}
    (hu : (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f) :
    ∃ (x₂ y₂ : F) (h₂ : W.Nonsingular x₂ y₂), Point.some x₂ y₂ h₂ ∈ W.torsion 2 ∧
      ∃ hpow : weilPairingElt h₂.left gS ^ 2 = 1, weilPairingMu h₂.left hpow ≠ 1 := by
  obtain ⟨x₂, y₂, h₂, hmem, hne⟩ :=
    exists_torsion_two_weilPairingElt_ne_one h2 h hf hfdiv hgS hu
  have hpow : weilPairingElt h₂.left gS ^ 2 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_two_torsion h₂.left h2
      (add_self_eq_zero_of_mem_torsion_two hmem) hgS hu
  exact ⟨x₂, y₂, h₂, hmem, hpow,
    fun hone => hne ((weilPairingMu_eq_one_iff h₂.left hpow).mp hone)⟩

open Classical in
/-- **Rung 5 and non-degeneracy in `μ_2(F)` together, with nothing carried**: for a nonsingular
affine `2`-torsion point `S` over an algebraically closed field of characteristic `≠ 2` there are a
principal `f_S` with `div f_S = 2·(S)`, a nonzero `g_S` with `u · g_S ^ 2 = [2]∗ f_S`, and an
**affine** `T ∈ E[2]` whose pairing value is a non-trivial square root of unity in `F`.

The `μ_2(F)` mirror of `exists_gS_two_weilPairingElt_ne_one`; the rung-5 half is
`exists_gS_two_of_isAlgClosed` (`#791`) in both. -/
theorem exists_gS_two_weilPairingMu_ne_one (h2 : (2 : F) ≠ 0) (h : W.Nonsingular x y)
    (hS : Point.some x y h ∈ W.torsion 2) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f) ∧
        ∃ (x₂ y₂ : F) (h₂ : W.Nonsingular x₂ y₂), Point.some x₂ y₂ h₂ ∈ W.torsion 2 ∧
          ∃ hpow : weilPairingElt h₂.left gS ^ 2 = 1, weilPairingMu h₂.left hpow ≠ 1 := by
  obtain ⟨f, hf, hfdiv, gS, hgS, u, hu⟩ := exists_gS_two_of_isAlgClosed h2 h hS
  exact ⟨f, hf, hfdiv, gS, hgS, ⟨u, hu⟩,
    exists_torsion_two_weilPairingMu_ne_one h2 h hf hfdiv hgS hu⟩

open Classical in
/-- **Silverman III.8.1(d) at `n = 2`, in `μ_2(F)`: `e_2(S, ·) ≡ 1` forces `S = O`.**

The `μ_2(F)` mirror of `eq_zero_of_forall_weilPairingElt_eq_one_two`, with the same
`pointDivisorAff`-uniform divisor hypothesis and the same freedom in `S`, which ranges over all of
`W.Point` with no torsion hypothesis.  See the module docstring for why the trivial-pairing
hypothesis quantifies over `hpow`. -/
theorem eq_zero_of_forall_weilPairingMu_eq_one_two (h2 : (2 : F) ≠ 0) {S : W.Point}
    {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = (2 : ℤ) • pointDivisorAff W S) (hgS : gS ≠ 0)
    {u : W.CoordinateRingˣ} (hu : (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f)
    (hone : ∀ (x₂ y₂ : F) (h₂ : W.Nonsingular x₂ y₂), Point.some x₂ y₂ h₂ ∈ W.torsion 2 →
      ∀ hpow : weilPairingElt h₂.left gS ^ 2 = 1, weilPairingMu h₂.left hpow = 1) :
    S = 0 :=
  eq_zero_of_forall_weilPairingElt_eq_one_two h2 hf hfdiv hgS hu fun x₂ y₂ h₂ hmem =>
    (weilPairingMu_eq_one_iff h₂.left
        (weilPairingElt_pow_eq_one_of_gS_two_torsion h₂.left h2
          (add_self_eq_zero_of_mem_torsion_two hmem) hgS hu)).mp
      (hone x₂ y₂ h₂ hmem _)

/-! ### `n = 3` -/

open Classical in
/-- **Non-degeneracy at `n = 3` in `μ_3(F)`, against an arbitrary rung-5 root**: some affine
`T ∈ E[3]` has `e_3(S, T) ≠ 1` as an element of `rootsOfUnity 3 F`.

The `n = 3` mirror of `exists_torsion_two_weilPairingMu_ne_one`; only the `hpow` producer differs,
`weilPairingElt_pow_eq_one_of_gS_three_baseField` (`TranslationTriplingComm`) in place of
`weilPairingElt_pow_eq_one_of_gS_two_torsion`.  The descent `weilPairingMu_eq_one_iff` is `n`-free
and is reused unchanged. -/
theorem exists_torsion_three_weilPairingMu_ne_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h : W.Nonsingular x y) {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ))
    (hgS : gS ≠ 0) {u : W.CoordinateRingˣ}
    (hu : (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f) :
    ∃ (x₃ y₃ : F) (h₃ : W.Nonsingular x₃ y₃), Point.some x₃ y₃ h₃ ∈ W.torsion 3 ∧
      ∃ hpow : weilPairingElt h₃.left gS ^ 3 = 1, weilPairingMu h₃.left hpow ≠ 1 := by
  obtain ⟨x₃, y₃, h₃, hmem, hne⟩ :=
    exists_torsion_three_weilPairingElt_ne_one h2 h3 h hf hfdiv hgS hu
  have hpow : weilPairingElt h₃.left gS ^ 3 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_three_baseField h₃.left h2 h3
      (add_add_self_eq_zero_of_mem_torsion_three hmem) hgS hu
  exact ⟨x₃, y₃, h₃, hmem, hpow,
    fun hone => hne ((weilPairingMu_eq_one_iff h₃.left hpow).mp hone)⟩

open Classical in
/-- **Rung 5 and non-degeneracy in `μ_3(F)` together, with nothing carried**: for a nonsingular
affine `3`-torsion point `S` over an algebraically closed field of characteristic `≠ 2, 3` there are
a principal `f_S` with `div f_S = 3·(S)`, a nonzero `g_S` with `u · g_S ^ 3 = [3]∗ f_S`, and an
**affine** `T ∈ E[3]` whose pairing value is a non-trivial cube root of unity in `F`.

The `μ_3(F)` mirror of `exists_gS_three_weilPairingElt_ne_one`; the rung-5 half is
`exists_gS_three_of_isAlgClosed` (`#825`) in both. -/
theorem exists_gS_three_weilPairingMu_ne_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion 3) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f) ∧
        ∃ (x₃ y₃ : F) (h₃ : W.Nonsingular x₃ y₃), Point.some x₃ y₃ h₃ ∈ W.torsion 3 ∧
          ∃ hpow : weilPairingElt h₃.left gS ^ 3 = 1, weilPairingMu h₃.left hpow ≠ 1 := by
  obtain ⟨f, hf, hfdiv, gS, hgS, u, hu⟩ := exists_gS_three_of_isAlgClosed h2 h3 h hS
  exact ⟨f, hf, hfdiv, gS, hgS, ⟨u, hu⟩,
    exists_torsion_three_weilPairingMu_ne_one h2 h3 h hf hfdiv hgS hu⟩

open Classical in
/-- **Silverman III.8.1(d) at `n = 3`, in `μ_3(F)`: `e_3(S, ·) ≡ 1` forces `S = O`.**

The `μ_3(F)` mirror of `eq_zero_of_forall_weilPairingElt_eq_one_three`.  As there, `S : W.Point` is
arbitrary — its torsion is what produces `f_S` and `g_S`, and those are hypotheses — and the divisor
condition is written with `pointDivisorAff`, which is `n`-free and sends `O` to `0`, so no case
split appears in the statement. -/
theorem eq_zero_of_forall_weilPairingMu_eq_one_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {S : W.Point} {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = (3 : ℤ) • pointDivisorAff W S) (hgS : gS ≠ 0)
    {u : W.CoordinateRingˣ} (hu : (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f)
    (hone : ∀ (x₃ y₃ : F) (h₃ : W.Nonsingular x₃ y₃), Point.some x₃ y₃ h₃ ∈ W.torsion 3 →
      ∀ hpow : weilPairingElt h₃.left gS ^ 3 = 1, weilPairingMu h₃.left hpow = 1) :
    S = 0 :=
  eq_zero_of_forall_weilPairingElt_eq_one_three h2 h3 hf hfdiv hgS hu fun x₃ y₃ h₃ hmem =>
    (weilPairingMu_eq_one_iff h₃.left
        (weilPairingElt_pow_eq_one_of_gS_three_baseField h₃.left h2 h3
          (add_add_self_eq_zero_of_mem_torsion_three hmem) hgS hu)).mp
      (hone x₃ y₃ h₃ hmem _)

end Nondegenerate

/-! ### Non-vacuity -/

section Nonvacuity

/-- An algebraically closed field of characteristic zero. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

/-- The curve `y² = x³ − x` over `AlgebraicClosure ℚ`, of discriminant `64`. -/
private noncomputable def exampleCurve : Affine exampleField := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The curve `y² + y = x³` over `AlgebraicClosure ℚ`, of discriminant `−27`. -/
private noncomputable def exampleCurveThree : Affine exampleField := ⟨0, 0, 1, 0, 0⟩

private instance : exampleCurveThree.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurveThree, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleTwo : (2 : exampleField) ≠ 0 := by norm_num

private lemma exampleThree : (3 : exampleField) ≠ 0 := by norm_num

/-- `S = (0, 0)` lies on `y² = x³ − x` and is nonsingular. -/
private lemma exampleNonsingular : exampleCurve.Nonsingular 0 0 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `S = (0, 0)` is `2`-torsion: `2y + a₁x + a₃ = 0` reads `0 = 0`. -/
private lemma exampleTorsion :
    Point.some (0 : exampleField) 0 exampleNonsingular ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNonsingular).mpr (by norm_num [exampleCurve])

/-- `S = (0, 0)` lies on `y² + y = x³` and is nonsingular. -/
private lemma exampleNonsingularThree : exampleCurveThree.Nonsingular 0 0 :=
  exampleCurveThree.equation_iff_nonsingular.mp (by
    norm_num [exampleCurveThree, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `S = (0, 0)` is `3`-torsion: `Ψ₃ = 3X⁴ + 3b₆X` vanishes at `0`, and the side condition of
`mem_torsion_three_some_iff` is automatic. -/
private lemma exampleTorsionThree :
    Point.some (0 : exampleField) 0 exampleNonsingularThree ∈ exampleCurveThree.torsion 3 :=
  mem_torsion_three_some_iff'.mpr (by
    norm_num [exampleCurveThree, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈])

open Classical in
/-- **Non-degeneracy at `n = 2` in `μ_2(F)`, on a curve that exists**, with the `2`-torsion point
named. -/
example : ∃ f : exampleCurve.FunctionField, f ≠ 0 ∧
    exampleCurve.divisor f
      = Finsupp.single (pointClosedPoint exampleNonsingular.left) (2 : ℤ) ∧
    ∃ gS : exampleCurve.FunctionField, gS ≠ 0 ∧
      (∃ u : exampleCurve.CoordinateRingˣ,
        (u : exampleCurve.CoordinateRing) • gS ^ 2 = mulByTwoEndo exampleTwo f) ∧
      ∃ (x₂ y₂ : exampleField) (h₂ : exampleCurve.Nonsingular x₂ y₂),
        Point.some x₂ y₂ h₂ ∈ exampleCurve.torsion 2 ∧
          ∃ hpow : weilPairingElt h₂.left gS ^ 2 = 1, weilPairingMu h₂.left hpow ≠ 1 :=
  exists_gS_two_weilPairingMu_ne_one exampleTwo exampleNonsingular exampleTorsion

open Classical in
/-- **Non-degeneracy at `n = 3` in `μ_3(F)`, on a curve that exists**, with the `3`-torsion point
named. -/
example : ∃ f : exampleCurveThree.FunctionField, f ≠ 0 ∧
    exampleCurveThree.divisor f
      = Finsupp.single (pointClosedPoint exampleNonsingularThree.left) (3 : ℤ) ∧
    ∃ gS : exampleCurveThree.FunctionField, gS ≠ 0 ∧
      (∃ u : exampleCurveThree.CoordinateRingˣ,
        (u : exampleCurveThree.CoordinateRing) • gS ^ 3
          = mulByThreeEndo exampleTwo exampleThree f) ∧
      ∃ (x₃ y₃ : exampleField) (h₃ : exampleCurveThree.Nonsingular x₃ y₃),
        Point.some x₃ y₃ h₃ ∈ exampleCurveThree.torsion 3 ∧
          ∃ hpow : weilPairingElt h₃.left gS ^ 3 = 1, weilPairingMu h₃.left hpow ≠ 1 :=
  exists_gS_three_weilPairingMu_ne_one exampleTwo exampleThree exampleNonsingularThree
    exampleTorsionThree

end Nonvacuity

end WeierstrassCurve.Affine
