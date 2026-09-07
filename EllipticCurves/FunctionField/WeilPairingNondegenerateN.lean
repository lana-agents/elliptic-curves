/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.CoordinateRingUnits
import EllipticCurves.FunctionField.DivisorConstant
import EllipticCurves.FunctionField.MulByNGalois
import EllipticCurves.FunctionField.PullbackPrincipalityN
import EllipticCurves.FunctionField.WeilPairingAlternating
import EllipticCurves.FunctionField.WeilPairingRootsOfUnity
import EllipticCurves.FunctionField.WeilPairingTranslationSlotHprinN

/-!
# Non-degeneracy of the Weil pairing at a general `n` over an algebraically closed field

Silverman *AEC* III.8, Prop. 8.1(c): if `e_n(S, T) = 1` for every `T ∈ E[n]` then `S = O`.

`EllipticCurves.FunctionField.WeilPairingNondegenerateTwo` (`#796`) and
`EllipticCurves.FunctionField.WeilPairingNondegenerateThree` (`#831`) prove it at `n = 2` and
`n = 3`.  This file proves it at **every** `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`, and the
two numeral layers are recovered from it below.

**Nothing new is proved here about curves.**  The content is the composition, and the care is in not
weakening any input's hypotheses along the way; see the Scope section, where the two places
`[IsAlgClosed F]` enters are named.

## The seven steps, and where each comes from

Let `S = (x, y)` be a nonsingular *affine* `n`-torsion point.  Affine means `S ≠ O`
(`Point.some_ne_zero`), which is the whole content of the conclusion `S = O`, contraposed.

1. **Rung 5, unconditionally.**  `exists_gS_n_of_isAlgClosed` and
   `exists_gS_of_ne_zero_of_isAlgClosed` (`PullbackPrincipalityN`, `#1843`) supply `f_S ≠ 0` with
   `div f_S = n·(S)` and `g_S ≠ 0` with `u · g_S ^ n = [n]∗ f_S`.  ⚠️ **This is the only step
   that was not already general**, and until
   PR #723 landed it was this file's whole obstruction.
2. **`e_n(S, T) = 1` *is* translation-invariance of `g_S`** —
   `weilPairingElt_eq_one_iff_translateEndo_fixed` (`WeilPairingAlternating`), unconditional and
   `n`-free: it mentions no isogeny at all.
3. **Invariance under every `T ∈ E[n]` is membership in `Fixed(E[n])`** — `mem_fixedFieldN_iff`
   (`MulByNGalois`) is `Iff.rfl`, and `torsionNMul_smul_def` / `translateAut_apply_some`
   (`TranslationActionN`) reduce the action to `translateEndo` by a case split on `W.Point`.  The
   point at infinity acts as the identity, so it carries no information — see the warning below.
4. **`Fixed(E[n]) = [n]∗F(W)`** — `fixedFieldN_eq_mulByNFieldRange_of_ne_zero` (`MulByNGalois`).
   So `g_S = [n]∗ q` for some `q`.  ⚠️ **That theorem is general in `n` and not `3`-smooth**: it
   carries `[IsAlgClosed F]`, `(2 : F) ≠ 0`, `(n : F) ≠ 0` and the transcendence of `x([n]𝒫)`, and
   nothing else.  It spends `finrank_mulByNFieldRange_eq_sq_of_two_ne_zero` against
   `finrank_fixedFieldN_of_ne_zero` and **states no torsion count at all** — see the Scope section
   on where `#242` really enters.
5. **Cancelling `[n]∗`.**  The unit `u` is a constant (`exists_eq_algebraMap_of_isUnit`), `[n]∗`
   fixes constants (`mulByNEndo_algebraMap_base`) and is injective (`mulByNEndo_injective`), so
   `c · q ^ n = f_S`.
6. **Divisors.**  `divisor_mul`, `divisor_algebraMap_base` and `divisor_pow` give
   `n • div q = n·(S)`, hence `div q = (S)` after cancelling `n` place by place.  All three are
   `n`-free.
7. **The contradiction.**  `not_exists_divisor_eq_single_pointClosedPoint` (`DivisorPrincipality`,
   `#726`): a single affine rational point is never a principal divisor.  This is the only step of
   the seven that *rules a function out* rather than exhibiting one, and it is `n`-free.

## Main statements

* `WeierstrassCurve.Affine.not_forall_torsionNMul_smul_eq` — the core, stated against an
  arbitrary rung-5 root rather than against `#1843`'s existential: a `g_S` with
  `u · g_S ^ n = [n]∗ f_S` over `div f_S = n·(S)` is **not** fixed by all of `E[n]`.
* `WeierstrassCurve.Affine.exists_torsion_n_weilPairingElt_ne_one` — the same in pairing
  language: some affine `T ∈ E[n]` has `e_n(S, T) ≠ 1`.
* `WeierstrassCurve.Affine.exists_gS_n_weilPairingElt_ne_one` — rung 5 and non-degeneracy
  together, with no hypothesis beyond the setting: for a nonsingular affine `n`-torsion `S` there
  are `f_S`, `g_S` as in rung 5 and an affine `T ∈ E[n]` with `e_n(S, T) ≠ 1`.
* **`WeierstrassCurve.Affine.eq_zero_of_forall_weilPairingElt_eq_one_n`** — Silverman's own shape:
  for `f_S` with `div f_S = n · pointDivisorAff S` and an `n`-th root `g_S` of `[n]∗ f_S` up to a
  unit, `e_n(S, ·) ≡ 1` on `E[n]` forces `S = O`.
* `WeierstrassCurve.Affine.exists_torsion_n_weilPairingMu_ne_one`,
  **`WeierstrassCurve.Affine.exists_gS_n_weilPairingMu_ne_one`** and
  `WeierstrassCurve.Affine.eq_zero_of_forall_weilPairingMu_eq_one_n` — the `μ_n(F)`-valued twins
  of the last three, mirroring the three headlines
  `EllipticCurves.FunctionField.WeilPairingNondegenerateMu` states at each of `n = 2`
  and `n = 3`.

⚠️ **The witness `T` is necessarily affine.**  At `T = O` the translation is the identity
(`translateAut_zero`) and `e_n(S, O) = 1` for trivial reasons, so a statement asserting
`∃ T ∈ E[n], e_n(S, T) ≠ 1` with `T` ranging over `W.Point` would still be true but a statement
proving it *at* `O` would be false.  Every conclusion below names an affine `T` by giving its
coordinates.

## Scope

⚠️ **`[IsAlgClosed F]` and `[W.IsElliptic]` are load-bearing, and the closure enters twice** —
through step 1 (`#1843`, itself through `[n]`-surjectivity on points *and* `#774`'s fibre
description at a general index) and independently through step 4
(`fixedFieldN_eq_mulByNFieldRange_of_ne_zero`, through `finrank_fixedFieldN_of_ne_zero`).
Removing either is not a matter of restating anything here.  Both numeral files record the same
two-source fact at their own index and this file inherits it unchanged.

⚠️ **`#242` enters this front through `#1843`, and only there.**  `card_torsion_eq_sq`
(`#E[n] = n²`, `EllipticCurves.Torsion.StructureGeneral`) is a **merged theorem**, and it is spent
by
`classOfDivisor_affinePart_pullbackDivisorN_eq_one` inside step 1 and by
`exists_nonsingular_mem_torsion` in the non-vacuity block below.  ⚠️ **Step 4 does not spend it**:
at `n = 2` the merged file's step 4 goes through `card_torsion_two`, which counts the roots of the
`2`-division cubic, and the general-`n` route replaces that with a `finrank` computation that states
no torsion count. `WeilPairingNondegenerateTwo`'s `## Scope` says of itself that it *"says nothing
about `#E[n] = n²` at general `n` (`#242`, `#1490`)"*; that sentence is about **its own** reach and
was written while `#242` was open, so it is history rather than a gate, and it does not describe
this file.

⚠️ **`hprin` over a general field (`#962`) is untouched and stays untouched.**  This is the
**index** axis over `F̄`, not the field axis: every theorem below carries `[IsAlgClosed F]`, exactly
as the two numeral files do.
`EllipticCurves.FunctionField.PullbackPrincipalityTwoRationalTorsion` carries the warning
*"It does not discharge `#962`, and must not be reported as doing so"*, and it binds here.

⚠️ **No two-slot pairing is added here, and none should be.**  `weilPairingTwoHom` /
`weilPairingThreeHom` (`#922`/`#925`) are the `W.Point × W.Point` pairings whose `ker = ⊥` consumes
the numeral headlines this file generalises; a general-`n` version of *those* is a separate question
with its own design decisions, and inventing a further spelling of the pairing is drift this front
has paid for before.  ⚠️ So the data-level statements here are the **input** to a point-level one,
not a substitute for it, which is why every headline below quantifies over the *data* `f_S`, `g_S`
that rung 5 produces: a caller holding its own root can apply it, whereas a point-level statement
has made that choice already.

⚠️ **This is not bilinearity, not the alternating property (`#465`), not Galois-equivariance
(`#456`), and not a perfect-pairing statement.**  Perfectness at `n = 2, 3` is
`bijective_weilPairing{Two,Three}Hom` (`EllipticCurves.FunctionField.WeilPairingPerfect`, `#940`),
which runs off `ker_weilPairing{Two,Three}Hom` and not off these headlines; nothing here narrows the
distance to a general-`n` form of it.

⚠️ **The statements below are pinned to `Classical.propDecidable`**, as all three merged
non-degeneracy files are: `open Classical in` is required, not decorative, because `TorsionNMul`
bakes the classical `DecidableEq F` instance in and the statements mention `W.torsion n`.

## ⚠️ Why the `μ_n(F)` twins carry `[NeZero n]` and the `F(W)` statements do not

`weilPairingMu` is indexed by `n` and takes `[NeZero n]` as an instance argument, so
`weilPairingMu hₙ.left hpow` does not *elaborate* without one.  The hypothesis is mathematically
free — `((n : ℤ) : F) ≠ 0` already forces `n ≠ 0` — but it cannot be derived inside the statement,
only inside a proof, so it is written into the binders.  This is the same shape, and the same
reason, as `weilPairingTorsionMuHom_n` (`WeilPairingTranslationSlotHprinN`).  The `hpow` binder in
the conclusions is the second half of the same phenomenon and is explained in
`EllipticCurves.FunctionField.WeilPairingNondegenerateMu`'s module docstring: `hpow` proves a
`Prop`, so the `∃ hpow`/`∀ hpow` forms assume nothing the `F(W)` statements do not.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8, Prop. 8.1(c).
-/

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

section Nondegenerate

variable [W.IsElliptic] [IsAlgClosed F] {n : ℕ} {x y : F}

open Classical in
/-- **The core of non-degeneracy at a general `n`: a rung-5 root of `f_S` is not `E[n]`-invariant.**

Given a nonsingular affine point `S = (x, y)`, a nonzero `f` with `div f = n·(S)`, and a `g_S` with
`u · g_S ^ n = [n]∗ f` for a unit `u` of `F[W]`, the translation action of `E[n]` does **not** fix
`g_S`.

Were it to, `g_S` would lie in `Fixed(E[n]) = [n]∗F(W)`
(`fixedFieldN_eq_mulByNFieldRange_of_ne_zero`), say `g_S = [n]∗ q`; the unit `u` is a constant `c`
(`exists_eq_algebraMap_of_isUnit`), `[n]∗` fixes constants and is injective, so `c · q ^ n = f` and
therefore `n • div q = n·(S)`.  Cancelling `n` place by place gives `div q = (S)`, and a single
affine rational point is never a principal divisor
(`not_exists_divisor_eq_single_pointClosedPoint`, `#726`).

Stated against an arbitrary rung-5 root rather than against `exists_gS_n_of_isAlgClosed`'s
existential, so that it applies to *any* function with the rung-5 property; `g_S ≠ 0` is not needed
here (it follows from `f ≠ 0`) and is not assumed.

⚠️ The transcendence datum `hT` is an explicit argument, as it is throughout
`EllipticCurves.FunctionField.PullbackPrincipalityN`, because `mulByNEndo` is indexed by it.  Over
`F̄` it is free at every `n ≠ 0` — see `exists_gS_n_weilPairingElt_ne_one`, which produces its
own. -/
theorem not_forall_torsionNMul_smul_eq (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    (hT : Transcendental F (n • genericPoint (W := W)).xCoord) (h : W.Nonsingular x y)
    {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ))
    {u : W.CoordinateRingˣ}
    (hu : (u : W.CoordinateRing) • gS ^ n = mulByNEndo n hT f) :
    ¬ ∀ T : TorsionNMul W n, T • gS = gS := by
  classical
  intro hfix
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
  have hn0 : n ≠ 0 := by rintro rfl; simp at hnF
  -- Steps 3 and 4: `g_S ∈ Fixed(E[n]) = [n]∗F(W)`.
  have hmem : gS ∈ fixedFieldN W n := mem_fixedFieldN_iff.mpr hfix
  rw [← fixedFieldN_eq_mulByNFieldRange_of_ne_zero h2 hnF hT] at hmem
  obtain ⟨q, hq⟩ := hmem
  have hq' : mulByNEndo n hT q = gS := hq
  clear hq
  -- Step 5: the unit is a constant, and `[n]∗` cancels.
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_isUnit u.isUnit
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact u.ne_zero (by rw [hc, map_zero])
  have hstep : algebraMap F W.FunctionField c * gS ^ n = mulByNEndo n hT f := by
    rw [← hu, Algebra.smul_def, hc, ← IsScalarTower.algebraMap_apply]
  have hpull : mulByNEndo n hT (algebraMap F W.FunctionField c * q ^ n) = mulByNEndo n hT f := by
    rw [map_mul, map_pow, mulByNEndo_algebraMap_base, hq', hstep]
  have heq : algebraMap F W.FunctionField c * q ^ n = f := mulByNEndo_injective n hT hpull
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hf (by rw [← heq]; simp [zero_pow hn0])
  have hcne : algebraMap F W.FunctionField c ≠ 0 := by simpa using hc0
  -- Step 6: `n • div q = n·(S)`, and `n` cancels place by place.
  have hdiv : n • divisor W q = Finsupp.single (pointClosedPoint h.left) (n : ℤ) := by
    rw [← hfdiv, ← heq, divisor_mul hcne (pow_ne_zero n hq0), divisor_algebraMap_base hc0,
      zero_add, divisor_pow]
  have hsingle : divisor W q = Finsupp.single (pointClosedPoint h.left) (1 : ℤ) := by
    ext v
    have hv := DFunLike.congr_fun hdiv v
    rw [Finsupp.smul_apply, nsmul_eq_mul] at hv
    refine mul_left_cancel₀ (a := (n : ℤ)) (by exact_mod_cast hn0) ?_
    rw [hv, Finsupp.single_apply, Finsupp.single_apply]
    split <;> simp
  -- Step 7: a single affine rational point is never principal.
  exact not_exists_divisor_eq_single_pointClosedPoint h ⟨q, hq0, hsingle⟩

open Classical in
/-- **Non-degeneracy at a general `n`, in pairing language**: some affine `T ∈ E[n]` has
`e_n(S, T) ≠ 1`.

Step 2 (`weilPairingElt_eq_one_iff_translateEndo_fixed`) turns each `e_n(S, T) = 1` into
`τ_T∗ g_S = g_S`, and step 3 assembles those into invariance under the whole action — the point at
infinity contributing nothing, since `translateAut 0` is the identity.  So a `g_S` pairing trivially
with every affine `n`-torsion point would be `E[n]`-invariant, which
`not_forall_torsionNMul_smul_eq` forbids.

⚠️ The witness is produced with its coordinates because it must be **affine**: `weilPairingElt` is
indexed by an `Equation`, and at `T = O` the element is `1` for trivial reasons. -/
theorem exists_torsion_n_weilPairingElt_ne_one (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    (hT : Transcendental F (n • genericPoint (W := W)).xCoord) (h : W.Nonsingular x y)
    {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ))
    (hgS : gS ≠ 0) {u : W.CoordinateRingˣ}
    (hu : (u : W.CoordinateRing) • gS ^ n = mulByNEndo n hT f) :
    ∃ (xₙ yₙ : F) (hₙ : W.Nonsingular xₙ yₙ), Point.some xₙ yₙ hₙ ∈ W.torsion n ∧
      weilPairingElt hₙ.left gS ≠ 1 := by
  classical
  by_contra hall
  push Not at hall
  refine not_forall_torsionNMul_smul_eq h2 hn hT h hf hfdiv hu fun T => ?_
  rw [torsionNMul_smul_def]
  have hmem : (T.toAdd : W.Point) ∈ W.torsion n := T.toAdd.2
  set P : W.Point := (T.toAdd : W.Point) with hP
  clear_value P
  cases P with
  | zero => rw [← Point.zero_def, translateAut_zero]; rfl
  | some xₙ yₙ hₙ =>
      rw [translateAut_apply_some]
      exact (weilPairingElt_eq_one_iff_translateEndo_fixed hₙ.left hgS).mp (hall _ _ hₙ hmem)

open Classical in
/-- **Rung 5 and non-degeneracy together, with nothing carried**: for a nonsingular affine
`n`-torsion point `S` over an algebraically closed field with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`
there are a principal function `f_S` with `div f_S = n·(S)`, a nonzero `g_S` with
`u · g_S ^ n = [n]∗ f_S`, and an **affine** `T ∈ E[n]` with `e_n(S, T) ≠ 1`.

This is the statement that could not be made before `#1843`: its rung-5 half is
`exists_gS_of_ne_zero_of_isAlgClosed`, which is `exists_gS_of_ne_zero` with `hprin` discharged.  The
transcendence datum is `transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`, matching that
theorem's own proof term so that the two `mulByNEndo` applications are syntactically equal. -/
theorem exists_gS_n_weilPairingElt_ne_one (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion n) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn) f) ∧
        ∃ (xₙ yₙ : F) (hₙ : W.Nonsingular xₙ yₙ), Point.some xₙ yₙ hₙ ∈ W.torsion n ∧
          weilPairingElt hₙ.left gS ≠ 1 := by
  obtain ⟨f, hf, hfdiv, gS, hgS, u, hu⟩ := exists_gS_of_ne_zero_of_isAlgClosed h2 hn h hS
  exact ⟨f, hf, hfdiv, gS, hgS, ⟨u, hu⟩,
    exists_torsion_n_weilPairingElt_ne_one h2 hn _ h hf hfdiv hgS hu⟩

open Classical in
/-- **Silverman III.8.1(c) at a general `n`: `e_n(S, ·) ≡ 1` forces `S = O`.**

`S : W.Point` is arbitrary — no torsion hypothesis is needed, because the torsion of `S` is what
produces `f_S` and `g_S` in the first place and those are hypotheses here.  The divisor condition is
written with `#791`'s `pointDivisorAff`, which is defined uniformly on `W.Point` and sends `O` to
`0`, so no case split appears in the statement: at an affine `S` it reads `div f_S = n·(S)`, and at
`S = O` it reads `div f_S = 0`, where the conclusion holds anyway.

⚠️ The trivial-pairing hypothesis quantifies over **affine** `n`-torsion points, which is not a
restriction: `e_n(S, O) = 1` always. -/
theorem eq_zero_of_forall_weilPairingElt_eq_one_n (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    (hT : Transcendental F (n • genericPoint (W := W)).xCoord) {S : W.Point}
    {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = (n : ℤ) • pointDivisorAff W S) (hgS : gS ≠ 0)
    {u : W.CoordinateRingˣ} (hu : (u : W.CoordinateRing) • gS ^ n = mulByNEndo n hT f)
    (hone : ∀ (xₙ yₙ : F) (hₙ : W.Nonsingular xₙ yₙ), Point.some xₙ yₙ hₙ ∈ W.torsion n →
      weilPairingElt hₙ.left gS = 1) :
    S = 0 := by
  cases S with
  | zero => rw [← Point.zero_def]
  | some x y h =>
      exfalso
      rw [pointDivisorAff_some, Finsupp.smul_single, smul_eq_mul, mul_one] at hfdiv
      obtain ⟨xₙ, yₙ, hₙ, hmem, hne⟩ :=
        exists_torsion_n_weilPairingElt_ne_one h2 hn hT h hf hfdiv hgS hu
      exact hne (hone xₙ yₙ hₙ hmem)

/-! ### The `μ_n(F)`-valued twins

The three headlines above restated as inequations in `rootsOfUnity n F`, mirroring the three
`WeilPairingNondegenerateMu` states at each of `n = 2` and `n = 3`.  **Nothing new is proved here**:
each is the descent `weilPairingMu_eq_one_iff` (`WeilPairingRootsOfUnity`, `#733`) applied to the
`F(W)` statement, and the `hpow` datum is produced from the rung-5 certificate `hu` the envelope
already carries by `weilPairingElt_pow_eq_one_of_gS_n_torsion`
(`WeilPairingTranslationSlotHprinN`, `#1843`) — the general-`n` producer, in place of the two
numeral ones `WeilPairingNondegenerateMu` uses.

⚠️ See the module docstring for why `[NeZero n]` appears here and not above. -/

variable [NeZero n]

open Classical in
/-- **Non-degeneracy at a general `n` in `μ_n(F)`, against an arbitrary rung-5 root**: some affine
`T ∈ E[n]` has `e_n(S, T) ≠ 1` as an element of `rootsOfUnity n F`.

The envelope is `exists_torsion_n_weilPairingElt_ne_one`'s, unchanged. -/
theorem exists_torsion_n_weilPairingMu_ne_one (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    (hT : Transcendental F (n • genericPoint (W := W)).xCoord) (h : W.Nonsingular x y)
    {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ))
    (hgS : gS ≠ 0) {u : W.CoordinateRingˣ}
    (hu : (u : W.CoordinateRing) • gS ^ n = mulByNEndo n hT f) :
    ∃ (xₙ yₙ : F) (hₙ : W.Nonsingular xₙ yₙ), Point.some xₙ yₙ hₙ ∈ W.torsion n ∧
      ∃ hpow : weilPairingElt hₙ.left gS ^ n = 1, weilPairingMu hₙ.left hpow ≠ 1 := by
  obtain ⟨xₙ, yₙ, hₙ, hmem, hne⟩ :=
    exists_torsion_n_weilPairingElt_ne_one h2 hn hT h hf hfdiv hgS hu
  have hpow : weilPairingElt hₙ.left gS ^ n = 1 :=
    weilPairingElt_pow_eq_one_of_gS_n_torsion hₙ.left n hT (mem_torsion_iff.mp hmem) hgS hu
  exact ⟨xₙ, yₙ, hₙ, hmem, hpow,
    fun hone => hne ((weilPairingMu_eq_one_iff hₙ.left hpow).mp hone)⟩

open Classical in
/-- **Rung 5 and non-degeneracy in `μ_n(F)` together, with nothing carried**: for a nonsingular
affine `n`-torsion point `S` over an algebraically closed field with `(2 : F) ≠ 0` and
`((n : ℤ) : F) ≠ 0` there are a principal `f_S` with `div f_S = n·(S)`, a nonzero `g_S` with
`u · g_S ^ n = [n]∗ f_S`, and an **affine** `T ∈ E[n]` whose pairing value is a non-trivial `n`-th
root of unity in `F`.

The `μ_n(F)` mirror of `exists_gS_n_weilPairingElt_ne_one`; the rung-5 half is
`exists_gS_of_ne_zero_of_isAlgClosed` (`#1843`) in both. -/
theorem exists_gS_n_weilPairingMu_ne_one (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion n) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn) f) ∧
        ∃ (xₙ yₙ : F) (hₙ : W.Nonsingular xₙ yₙ), Point.some xₙ yₙ hₙ ∈ W.torsion n ∧
          ∃ hpow : weilPairingElt hₙ.left gS ^ n = 1, weilPairingMu hₙ.left hpow ≠ 1 := by
  obtain ⟨f, hf, hfdiv, gS, hgS, u, hu⟩ := exists_gS_of_ne_zero_of_isAlgClosed h2 hn h hS
  exact ⟨f, hf, hfdiv, gS, hgS, ⟨u, hu⟩,
    exists_torsion_n_weilPairingMu_ne_one h2 hn _ h hf hfdiv hgS hu⟩

open Classical in
/-- **Silverman III.8.1(c) at a general `n`, in `μ_n(F)`: `e_n(S, ·) ≡ 1` forces `S = O`.**

The `μ_n(F)` mirror of `eq_zero_of_forall_weilPairingElt_eq_one_n`, with the same
`pointDivisorAff`-uniform divisor hypothesis and the same freedom in `S`, which ranges over all of
`W.Point` with no torsion hypothesis. -/
theorem eq_zero_of_forall_weilPairingMu_eq_one_n (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    (hT : Transcendental F (n • genericPoint (W := W)).xCoord) {S : W.Point}
    {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = (n : ℤ) • pointDivisorAff W S) (hgS : gS ≠ 0)
    {u : W.CoordinateRingˣ} (hu : (u : W.CoordinateRing) • gS ^ n = mulByNEndo n hT f)
    (hone : ∀ (xₙ yₙ : F) (hₙ : W.Nonsingular xₙ yₙ), Point.some xₙ yₙ hₙ ∈ W.torsion n →
      ∀ hpow : weilPairingElt hₙ.left gS ^ n = 1, weilPairingMu hₙ.left hpow = 1) :
    S = 0 :=
  eq_zero_of_forall_weilPairingElt_eq_one_n h2 hn hT hf hfdiv hgS hu fun xₙ yₙ hₙ hmem =>
    (weilPairingMu_eq_one_iff hₙ.left
        (weilPairingElt_pow_eq_one_of_gS_n_torsion hₙ.left n hT (mem_torsion_iff.mp hmem)
          hgS hu)).mp
      (hone xₙ yₙ hₙ hmem _)

/-! ### Recovery of the two merged numeral layers, compiled

⚠️ **The containment is committed here rather than asserted in a docstring**, following
`EllipticCurves.FunctionField.PullbackPrincipalityN` and
`EllipticCurves.FunctionField.MulByNFibre`, which do the same on their fronts.  Each `example`
restates a merged headline **verbatim** and proves it from the general layer.

⚠️ **The two `mulByNEndo` terms carry different transcendence proofs**, and they are interchangeable
because `Transcendental` is a `Prop`; that is what makes these typecheck at all.  The bridges to the
merged numeral endomorphisms are `mulByNEndo_two` and `mulByNEndo_three`
(`EllipticCurves.FunctionField.MulByNPullback`).

⚠️ **Neither original `omit`s anything from the ambient block**, so these carry the same instances
their originals do.  That was checked against the `omit` lines of `WeilPairingNondegenerateTwo`,
`WeilPairingNondegenerateThree` and `WeilPairingNondegenerateMu` — all three have none, and all
three declare exactly `variable [W.IsElliptic] [IsAlgClosed F] {x y : F}` — not by comparing
signature strings: an `example` that quietly keeps an instance its original omits restates something
*weaker* than the theorem it claims to subsume, and the signatures match either way.

⚠️ **The `μ_n(F)` twins are recovered too**, at the Silverman headline, because that is the one
whose hypothesis is a universal and so the one where a mismatch would be invisible. -/

open Classical in
/-- **`exists_gS_two_weilPairingElt_ne_one` is a corollary of `exists_gS_n_weilPairingElt_ne_one`**
— its statement verbatim, proved from the general layer. -/
example (h2 : (2 : F) ≠ 0) (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion 2) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f) ∧
        ∃ (x₂ y₂ : F) (h₂ : W.Nonsingular x₂ y₂), Point.some x₂ y₂ h₂ ∈ W.torsion 2 ∧
          weilPairingElt h₂.left gS ≠ 1 := by
  obtain ⟨f, hf, hfdiv, gS, hgS, ⟨u, hu⟩, w⟩ :=
    exists_gS_n_weilPairingElt_ne_one (W := W) (n := 2) h2 (by exact_mod_cast h2) h hS
  exact ⟨f, hf, by exact_mod_cast hfdiv, gS, hgS,
    ⟨u, by rw [hu, ← mulByNEndo_two h2]⟩, w⟩

open Classical in
/-- **`exists_gS_three_weilPairingElt_ne_one` is a corollary of
`exists_gS_n_weilPairingElt_ne_one`** — its statement verbatim, proved from the general layer. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (h : W.Nonsingular x y)
    (hS : Point.some x y h ∈ W.torsion 3) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f) ∧
        ∃ (x₃ y₃ : F) (h₃ : W.Nonsingular x₃ y₃), Point.some x₃ y₃ h₃ ∈ W.torsion 3 ∧
          weilPairingElt h₃.left gS ≠ 1 := by
  obtain ⟨f, hf, hfdiv, gS, hgS, ⟨u, hu⟩, w⟩ :=
    exists_gS_n_weilPairingElt_ne_one (W := W) (n := 3) h2 (by exact_mod_cast h3) h hS
  exact ⟨f, hf, by exact_mod_cast hfdiv, gS, hgS,
    ⟨u, by rw [hu, ← mulByNEndo_three h2 h3]⟩, w⟩

open Classical in
/-- **`eq_zero_of_forall_weilPairingElt_eq_one_two` is a corollary of
`eq_zero_of_forall_weilPairingElt_eq_one_n`** — its statement verbatim, proved from the general
layer. -/
example (h2 : (2 : F) ≠ 0) {S : W.Point} {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = (2 : ℤ) • pointDivisorAff W S) (hgS : gS ≠ 0)
    {u : W.CoordinateRingˣ} (hu : (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f)
    (hone : ∀ (x₂ y₂ : F) (h₂ : W.Nonsingular x₂ y₂), Point.some x₂ y₂ h₂ ∈ W.torsion 2 →
      weilPairingElt h₂.left gS = 1) :
    S = 0 :=
  eq_zero_of_forall_weilPairingElt_eq_one_n (n := 2) h2 (by exact_mod_cast h2)
    (transcendental_xCoord_two_nsmul h2) hf (by exact_mod_cast hfdiv) hgS
    (by rw [hu, ← mulByNEndo_two h2]) hone

open Classical in
/-- **`eq_zero_of_forall_weilPairingElt_eq_one_three` is a corollary of
`eq_zero_of_forall_weilPairingElt_eq_one_n`** — its statement verbatim, proved from the general
layer. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {S : W.Point} {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = (3 : ℤ) • pointDivisorAff W S) (hgS : gS ≠ 0)
    {u : W.CoordinateRingˣ} (hu : (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f)
    (hone : ∀ (x₃ y₃ : F) (h₃ : W.Nonsingular x₃ y₃), Point.some x₃ y₃ h₃ ∈ W.torsion 3 →
      weilPairingElt h₃.left gS = 1) :
    S = 0 :=
  eq_zero_of_forall_weilPairingElt_eq_one_n (n := 3) h2 (by exact_mod_cast h3)
    (transcendental_xCoord_three_nsmul h2 h3) hf (by exact_mod_cast hfdiv) hgS
    (by rw [hu, ← mulByNEndo_three h2 h3]) hone

open Classical in
/-- **`eq_zero_of_forall_weilPairingMu_eq_one_two` is a corollary of
`eq_zero_of_forall_weilPairingMu_eq_one_n`** — its statement verbatim, proved from the general
layer. -/
example (h2 : (2 : F) ≠ 0) {S : W.Point} {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = (2 : ℤ) • pointDivisorAff W S) (hgS : gS ≠ 0)
    {u : W.CoordinateRingˣ} (hu : (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f)
    (hone : ∀ (x₂ y₂ : F) (h₂ : W.Nonsingular x₂ y₂), Point.some x₂ y₂ h₂ ∈ W.torsion 2 →
      ∀ hpow : weilPairingElt h₂.left gS ^ 2 = 1, weilPairingMu h₂.left hpow = 1) :
    S = 0 :=
  eq_zero_of_forall_weilPairingMu_eq_one_n (n := 2) h2 (by exact_mod_cast h2)
    (transcendental_xCoord_two_nsmul h2) hf (by exact_mod_cast hfdiv) hgS
    (by rw [hu, ← mulByNEndo_two h2]) hone

open Classical in
/-- **`eq_zero_of_forall_weilPairingMu_eq_one_three` is a corollary of
`eq_zero_of_forall_weilPairingMu_eq_one_n`** — its statement verbatim, proved from the general
layer. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {S : W.Point} {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = (3 : ℤ) • pointDivisorAff W S) (hgS : gS ≠ 0)
    {u : W.CoordinateRingˣ} (hu : (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f)
    (hone : ∀ (x₃ y₃ : F) (h₃ : W.Nonsingular x₃ y₃), Point.some x₃ y₃ h₃ ∈ W.torsion 3 →
      ∀ hpow : weilPairingElt h₃.left gS ^ 3 = 1, weilPairingMu h₃.left hpow = 1) :
    S = 0 :=
  eq_zero_of_forall_weilPairingMu_eq_one_n (n := 3) h2 (by exact_mod_cast h3)
    (transcendental_xCoord_three_nsmul h2 h3) hf (by exact_mod_cast hfdiv) hgS
    (by rw [hu, ← mulByNEndo_three h2 h3]) hone

end Nondegenerate

/-! ### Non-vacuity at an index outside `{2, 3}`

⚠️ **A certificate at `n = 2` or `n = 3` would prove nothing the two merged files do not**, so the
witness has to be produced at an index neither of them reaches.  `#1843`'s
`exists_nonsingular_mem_torsion` supplies one **over `F̄` at every `n ≠ 0, 1` with `(2 : F) ≠ 0`
and `(n : F) ≠ 0`** — its own headline's words, and the two field conditions are part of what it
reaches and not of an ambient setting: `#E[n] = n² > 1` (`card_torsion_eq_sq`, `#242`) makes `E[n]`
nontrivial, and a nonzero point of `W.Point` is a `Point.some` by construction.  ⚠️ **Naming the
index condition alone would be false and not merely partial**, which is why it is not named alone
here: at `n = char F` the index condition holds and no affine `n`-torsion point is supplied, because
the count it is produced from fails there — of `#E[n] = n²`, `PullbackPrincipalityN` says *"at
`n = char F` the latter is **false**, not merely unproved"*.

⚠️ **The point is not nameable at `n = 5`**, and the certificate below is stated at a *quantified*
`(x, y)` rather than exhibiting coordinates the way `WeilPairingNondegenerateTwo` exhibits `(0, 0)`.
Faking a closed form here is exactly what `exists_nonsingular_mem_torsion` being an existence
statement exists to prevent. -/

section Nonvacuity

/-! The certificate curve `y² + y = x³` is the shared `EllipticCurves.Fixture.y2AddYEqX3` and the
base — algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `5 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here. -/

open EllipticCurves.Fixture

open Classical in
/-- **Non-degeneracy at `n = 5`, on a curve that exists**: the headline at an index neither merged
numeral file reaches, over `AlgebraicClosure ℚ`.  ⚠️ The `5`-torsion point `S` is produced by
`exists_nonsingular_mem_torsion` and not exhibited. -/
example : ∃ (x y : AlgClosedQ) (h : (y2AddYEqX3 AlgClosedQ).Nonsingular x y),
    ∃ f : (y2AddYEqX3 AlgClosedQ).FunctionField, f ≠ 0 ∧
      (y2AddYEqX3 AlgClosedQ).divisor f
        = Finsupp.single (pointClosedPoint h.left) (5 : ℤ) ∧
      ∃ gS : (y2AddYEqX3 AlgClosedQ).FunctionField, gS ≠ 0 ∧
        (∃ u : (y2AddYEqX3 AlgClosedQ).CoordinateRingˣ,
          (u : (y2AddYEqX3 AlgClosedQ).CoordinateRing) • gS ^ 5
            = mulByNEndo 5 (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero
                (W := y2AddYEqX3 AlgClosedQ) (by norm_num) (by norm_num)) f) ∧
        ∃ (x₅ y₅ : AlgClosedQ) (h₅ : (y2AddYEqX3 AlgClosedQ).Nonsingular x₅ y₅),
          Point.some x₅ y₅ h₅ ∈ (y2AddYEqX3 AlgClosedQ).torsion 5 ∧
            weilPairingElt h₅.left gS ≠ 1 := by
  classical
  obtain ⟨x, y, h, hS⟩ :=
    exists_nonsingular_mem_torsion (W := y2AddYEqX3 AlgClosedQ) (n := 5)
      (by norm_num) (by norm_num) (by norm_num)
  exact ⟨x, y, h, exists_gS_n_weilPairingElt_ne_one (by norm_num) (by norm_num) h hS⟩

end Nonvacuity

end WeierstrassCurve.Affine
