/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.CoordinateRingUnits
import EllipticCurves.FunctionField.DivisorConstant
import EllipticCurves.FunctionField.MulByTwoGalois
import EllipticCurves.FunctionField.PullbackPrincipalityTwo
import EllipticCurves.FunctionField.WeilPairingAlternating

/-!
# Non-degeneracy of the Weil pairing at `n = 2` over an algebraically closed field

Silverman *AEC* III.8, Prop. 8.1(c): if `e_n(S, T) = 1` for every `T ∈ E[n]` then `S = O`.

`EllipticCurves.FunctionField.WeilPairing`'s scope section reads that argument at `n = 2` as seven
steps and records, for each, what supplies it.  Until `#791` step 1 was conditional — rung 5's
`exists_gS_two` carried the principality hypothesis `hprin` — and every other step was merged.  This
file is the assembly, now that step 1 is unconditional over an algebraically closed base field.

**Nothing new is proved here about curves.**  The content is the composition, and the care is in not
weakening any input's hypotheses along the way; see the Scope section, where the two places
`[IsAlgClosed F]` enters are named.

## The seven steps, and where each comes from

Let `S = (x, y)` be a nonsingular *affine* `2`-torsion point.  Affine means `S ≠ O`
(`Point.some_ne_zero`), which is the whole content of the conclusion `S = O`, contraposed.

1. **Rung 5, unconditionally.**  `exists_gS_two_of_isAlgClosed` (`PullbackPrincipalityTwo`, `#791`)
   supplies `f_S ≠ 0` with `div f_S = 2·(S)` and `g_S ≠ 0` with `u · g_S ^ 2 = [2]∗ f_S`.
2. **`e_2(S, T) = 1` *is* translation-invariance of `g_S`** —
   `weilPairingElt_eq_one_iff_translateEndo_fixed` (`WeilPairingAlternating`), unconditional.
3. **Invariance under every `T ∈ E[2]` is membership in `Fixed(E[2])`** — `mem_fixedFieldTwo_iff`
   is `Iff.rfl`, and `torsionTwoMul_smul_def` / `translateAut_apply_some` (`TranslationAction`)
   reduce the action to `translateEndo` by a case split on `W.Point`.  The point at infinity acts as
   the identity, so it carries no information — see the warning below.
4. **`Fixed(E[2]) = [2]∗F(W)`** — `fixedFieldTwo_eq_mulByTwoFieldRange` (`MulByTwoGalois`, `#759`),
   Artin against `card_torsion_two`.  So `g_S = [2]∗ q` for some `q`.
5. **Cancelling `[2]∗`.**  The unit `u` is a constant (`exists_eq_algebraMap_of_isUnit`), `[2]∗`
   fixes constants (`mulByTwoEndo_algebraMap_base`) and is injective, so `c · q ^ 2 = f_S`.
6. **Divisors.**  `divisor_mul`, `divisor_algebraMap_base` and `divisor_pow` give
   `2 • div q = 2·(S)`, hence `div q = (S)` after cancelling `2` place by place.
7. **The contradiction.**  `not_exists_divisor_eq_single_pointClosedPoint` (`DivisorPrincipality`,
   `#726`): a single affine rational point is never a principal divisor.  This is the only step of
   the seven that *rules a function out* rather than exhibiting one.

## Main statements

* `WeierstrassCurve.Affine.not_forall_torsionTwoMul_smul_eq` — the core, stated against an
  arbitrary rung-5 root rather than against `#791`'s existential: a `g_S` with
  `u · g_S ^ 2 = [2]∗ f_S` over `div f_S = 2·(S)` is **not** fixed by all of `E[2]`.
* `WeierstrassCurve.Affine.exists_torsion_two_weilPairingElt_ne_one` — the same in pairing
  language: some affine `T ∈ E[2]` has `e_2(S, T) ≠ 1`.
* `WeierstrassCurve.Affine.exists_gS_two_weilPairingElt_ne_one` — rung 5 and non-degeneracy
  together, with no hypothesis beyond the setting: for a nonsingular affine `2`-torsion `S` there
  are `f_S`, `g_S` as in rung 5 and an affine `T ∈ E[2]` with `e_2(S, T) ≠ 1`.
* **`WeierstrassCurve.Affine.eq_zero_of_forall_weilPairingElt_eq_one_two`** — Silverman's own shape:
  for `f_S` with `div f_S = 2 · pointDivisorAff S` and a square root `g_S` of `[2]∗ f_S` up to a
  unit, `e_2(S, ·) ≡ 1` on `E[2]` forces `S = O`.

⚠️ **The witness `T` is necessarily affine.**  At `T = O` the translation is the identity
(`translateAut_zero`) and `e_2(S, O) = 1` for trivial reasons, so a statement asserting
`∃ T ∈ E[2], e_2(S, T) ≠ 1` with `T` ranging over `W.Point` would still be true but a statement
proving it *at* `O` would be false.  Every conclusion below names an affine `T` by giving its
coordinates.

## Scope

⚠️ **`n = 2` only, and the `n = 3` mirror now exists.**  At `n = 3` steps 3 and 4 transpose —
`mem_fixedFieldThree_iff` and `fixedFieldThree_eq_mulByThreeFieldRange` (`MulByThreeGalois`,
`#784`) — and step 1's `hprin` is discharged over an algebraically closed base field by
`EllipticCurves.FunctionField.PullbackPrincipalityThree` (`#825`).  The assembly those four inputs
were waiting for is `EllipticCurves.FunctionField.WeilPairingNondegenerateThree` (`#831`), which
transposes all seven steps below with `2 ↦ 3` and adds `(3 : F) ≠ 0`.  ⚠️ This bullet used to say
that nothing in the tree stated non-degeneracy at `n = 3` and that the assembly had not been
attempted; that was true for five merges and is what `#831` was filed to end.  Nothing here changed
to make it possible — the mirror was always an assembly and never a research step.

⚠️ **`[IsAlgClosed F]` and `[W.IsElliptic]` are load-bearing, and the closure enters twice** —
through step 1 (`#791`, itself through `exists_nsmul_two_eq` and `#774`'s fibre description) and
independently through step 4 (`#759`, through `card_torsion_two`).  Removing either is not a
matter of restating anything here.  In particular `WeilPairing.lean` carries `[W.IsElliptic]` but
**not** `[IsAlgClosed F]`, so this statement could not have landed there: a sentence — or a theorem
— inherits the variable block of the file it lands in (`#788`).

⚠️ **This is not bilinearity, not the alternating property (`#465`), not Galois-equivariance
(`#456`), and not general `n`.**  It says nothing about `#E[n] = n²` at general `n` (`#242`,
`#1490`; ⚠️ **not** `#404` and **not** Ward, both closed, and no longer `#251`, closed too): the
only count it uses is
`card_torsion_two`, inside `#759`, which counts the roots
of the `2`-division cubic and does not go through Ward.

⚠️ **There now IS a `W.Point`-level pairing in this tree, and this file's headline is what its
non-degeneracy consumes.**  This section used to say the opposite — *"there is no `W.Point`-level
pairing in this tree, so non-degeneracy cannot be stated as a property of a bilinear map"* — and
`EllipticCurves.FunctionField.WeilPairingFunctionTwo` (`#922`) was written to remove it.  That file
defines `weilPairingTwo : E[2] → E[2] → μ_2(F)` as a genuine function of two torsion points, bundles
it as `weilPairingTwoHom`, and states `ker_weilPairingTwoHom h2 = ⊥`, which is precisely the
property of a bilinear map.  Its proof reaches `eq_zero_of_forall_weilPairingElt_eq_one_two` below
in three steps and consumes nothing else — `ker_weilPairingTwoHom`, then
`eq_zero_of_forall_weilPairingTwo_eq_one`, then `eq_zero_of_forall_weilPairingEltTwo_eq_one`, which
applies it to the chosen root.

⚠️ **So the data-level statement here is the *input* to the point-level one, not a substitute for
it**, and it is worth keeping in that shape: it quantifies over the *data* `f_S`, `g_S` that rung 5
produces, so a caller holding its own root can apply it, whereas the point-level statement has made
that choice already.  ⚠️ **The reason the two fit together with no divisor bookkeeping is `hfdiv`
below**: `divisor W f = (2 : ℤ) • pointDivisorAff W S`, with `S : W.Point`, is the one shape that
covers `O` and the affine points at once, which is why `#922` could take it as its root predicate
verbatim.

⚠️ Inventing a *further* spelling of the pairing here would still be the drift this front keeps
paying for; the packaging work belongs in `WeilPairingFunctionTwo` and was done there.

⚠️ **This bullet used to end** *"At `n = 3` there is still no such pairing — `#922` is `n = 2`
only — so `EllipticCurves.FunctionField.WeilPairingNondegenerateThree` remains the closest
statement at that index."*  **Both conjuncts are false.**  `weilPairingThree : E[3] → E[3] → μ_3(F)`
exists, with `ker_weilPairingThreeHom = ⊥`, in
`EllipticCurves.FunctionField.WeilPairingFunctionThree` (`#925`) — the `n = 3` mirror of `#922`,
written thirty-four minutes after this sentence was.  And `WeilPairingNondegenerateThree` is
therefore not *"the closest statement at that index"* but the **input** `#925` consumes, standing
to it exactly as this file stands to `#922`; its own docstring already says so, in the same wording
this `## Scope` section uses for the `n = 2` pair.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8, Prop. 8.1(c).
-/

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

section Nondegenerate

variable [W.IsElliptic] [IsAlgClosed F] {x y : F}

open Classical in
/-- **The core of non-degeneracy at `n = 2`: a rung-5 root of `f_S` is not `E[2]`-invariant.**

Given a nonsingular affine point `S = (x, y)`, a nonzero `f` with `div f = 2·(S)`, and a nonzero
`g_S` with `u · g_S ^ 2 = [2]∗ f` for a unit `u` of `F[W]`, the translation action of `E[2]` does
**not** fix `g_S`.

Were it to, `g_S` would lie in `Fixed(E[2]) = [2]∗F(W)` (`fixedFieldTwo_eq_mulByTwoFieldRange`,
`#759`), say `g_S = [2]∗ q`; the unit `u` is a constant `c` (`exists_eq_algebraMap_of_isUnit`),
`[2]∗` fixes constants and is injective, so `c · q ^ 2 = f` and therefore `2 • div q = 2·(S)`.
Cancelling `2` place by place gives `div q = (S)`, and a single affine rational point is never a
principal divisor (`not_exists_divisor_eq_single_pointClosedPoint`, `#726`).

Stated against an arbitrary rung-5 root rather than against `exists_gS_two_of_isAlgClosed`'s
existential, so that it applies to *any* function with the rung-5 property; `g_S ≠ 0` is not needed
here (it follows from `f ≠ 0`) and is not assumed. -/
theorem not_forall_torsionTwoMul_smul_eq (h2 : (2 : F) ≠ 0) (h : W.Nonsingular x y)
    {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ))
    {u : W.CoordinateRingˣ}
    (hu : (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f) :
    ¬ ∀ T : TorsionTwoMul W, T • gS = gS := by
  classical
  intro hfix
  -- Steps 3 and 4: `g_S ∈ Fixed(E[2]) = [2]∗F(W)`.
  have hmem : gS ∈ fixedFieldTwo W := mem_fixedFieldTwo_iff.mpr hfix
  rw [← fixedFieldTwo_eq_mulByTwoFieldRange h2] at hmem
  obtain ⟨q, hq⟩ := hmem
  have hq' : mulByTwoEndo h2 q = gS := hq
  clear hq
  -- Step 5: the unit is a constant, and `[2]∗` cancels.
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_isUnit u.isUnit
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact u.ne_zero (by rw [hc, map_zero])
  have hstep : algebraMap F W.FunctionField c * gS ^ 2 = mulByTwoEndo h2 f := by
    rw [← hu, Algebra.smul_def, hc, ← IsScalarTower.algebraMap_apply]
  have hpull : mulByTwoEndo h2 (algebraMap F W.FunctionField c * q ^ 2) = mulByTwoEndo h2 f := by
    rw [map_mul, map_pow, mulByTwoEndo_algebraMap_base, hq', hstep]
  have heq : algebraMap F W.FunctionField c * q ^ 2 = f := (mulByTwoEndo h2).injective hpull
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hf (by rw [← heq]; ring)
  have hcne : algebraMap F W.FunctionField c ≠ 0 := by simpa using hc0
  -- Step 6: `2 • div q = 2·(S)`, and `2` cancels place by place.
  have hdiv : (2 : ℕ) • divisor W q = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) := by
    rw [← hfdiv, ← heq, divisor_mul hcne (pow_ne_zero 2 hq0), divisor_algebraMap_base hc0,
      zero_add, divisor_pow]
  have hsingle : divisor W q = Finsupp.single (pointClosedPoint h.left) (1 : ℤ) := by
    ext v
    have hv := DFunLike.congr_fun hdiv v
    rw [Finsupp.smul_apply, nsmul_eq_mul] at hv
    push_cast at hv
    refine mul_left_cancel₀ (a := (2 : ℤ)) (by norm_num) ?_
    rw [hv, Finsupp.single_apply, Finsupp.single_apply]
    split <;> norm_num
  -- Step 7: a single affine rational point is never principal.
  exact not_exists_divisor_eq_single_pointClosedPoint h ⟨q, hq0, hsingle⟩

open Classical in
/-- **Non-degeneracy at `n = 2`, in pairing language**: some affine `T ∈ E[2]` has
`e_2(S, T) ≠ 1`.

Step 2 (`weilPairingElt_eq_one_iff_translateEndo_fixed`) turns each `e_2(S, T) = 1` into
`τ_T∗ g_S = g_S`, and step 3 assembles those into invariance under the whole action — the point at
infinity contributing nothing, since `translateAut 0` is the identity.  So a `g_S` pairing trivially
with every affine `2`-torsion point would be `E[2]`-invariant, which
`not_forall_torsionTwoMul_smul_eq` forbids.

⚠️ The witness is produced with its coordinates because it must be **affine**: `weilPairingElt` is
indexed by an `Equation`, and at `T = O` the element is `1` for trivial reasons. -/
theorem exists_torsion_two_weilPairingElt_ne_one (h2 : (2 : F) ≠ 0) (h : W.Nonsingular x y)
    {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ))
    (hgS : gS ≠ 0) {u : W.CoordinateRingˣ}
    (hu : (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f) :
    ∃ (x₂ y₂ : F) (h₂ : W.Nonsingular x₂ y₂), Point.some x₂ y₂ h₂ ∈ W.torsion 2 ∧
      weilPairingElt h₂.left gS ≠ 1 := by
  classical
  by_contra hall
  push Not at hall
  refine not_forall_torsionTwoMul_smul_eq h2 h hf hfdiv hu fun T => ?_
  rw [torsionTwoMul_smul_def]
  have hmem : (T.toAdd : W.Point) ∈ W.torsion 2 := T.toAdd.2
  set P : W.Point := (T.toAdd : W.Point) with hP
  clear_value P
  cases P with
  | zero => rw [← Point.zero_def, translateAut_zero]; rfl
  | some x₂ y₂ h₂ =>
      rw [translateAut_apply_some]
      exact (weilPairingElt_eq_one_iff_translateEndo_fixed h₂.left hgS).mp (hall _ _ h₂ hmem)

open Classical in
/-- **Rung 5 and non-degeneracy together, with nothing carried**: for a nonsingular affine
`2`-torsion point `S` over an algebraically closed field of characteristic `≠ 2` there are a
principal function `f_S` with `div f_S = 2·(S)`, a nonzero `g_S` with `u · g_S ^ 2 = [2]∗ f_S`, and
an **affine** `T ∈ E[2]` with `e_2(S, T) ≠ 1`.

This is the statement that could not be made before `#791`: its rung-5 half is
`exists_gS_two_of_isAlgClosed`, which is `exists_gS_two` with `hprin` discharged. -/
theorem exists_gS_two_weilPairingElt_ne_one (h2 : (2 : F) ≠ 0) (h : W.Nonsingular x y)
    (hS : Point.some x y h ∈ W.torsion 2) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f) ∧
        ∃ (x₂ y₂ : F) (h₂ : W.Nonsingular x₂ y₂), Point.some x₂ y₂ h₂ ∈ W.torsion 2 ∧
          weilPairingElt h₂.left gS ≠ 1 := by
  obtain ⟨f, hf, hfdiv, gS, hgS, u, hu⟩ := exists_gS_two_of_isAlgClosed h2 h hS
  exact ⟨f, hf, hfdiv, gS, hgS, ⟨u, hu⟩,
    exists_torsion_two_weilPairingElt_ne_one h2 h hf hfdiv hgS hu⟩

open Classical in
/-- **Silverman III.8.1(c) at `n = 2`: `e_2(S, ·) ≡ 1` forces `S = O`.**

`S : W.Point` is arbitrary — no torsion hypothesis is needed, because the torsion of `S` is what
produces `f_S` and `g_S` in the first place and those are hypotheses here.  The divisor condition is
written with `#791`'s `pointDivisorAff`, which is defined uniformly on `W.Point` and sends `O` to
`0`, so no case split appears in the statement: at an affine `S` it reads `div f_S = 2·(S)`, and at
`S = O` it reads `div f_S = 0`, where the conclusion holds anyway.

⚠️ The trivial-pairing hypothesis quantifies over **affine** `2`-torsion points, which is not a
restriction: `e_2(S, O) = 1` always. -/
theorem eq_zero_of_forall_weilPairingElt_eq_one_two (h2 : (2 : F) ≠ 0) {S : W.Point}
    {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = (2 : ℤ) • pointDivisorAff W S) (hgS : gS ≠ 0)
    {u : W.CoordinateRingˣ} (hu : (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f)
    (hone : ∀ (x₂ y₂ : F) (h₂ : W.Nonsingular x₂ y₂), Point.some x₂ y₂ h₂ ∈ W.torsion 2 →
      weilPairingElt h₂.left gS = 1) :
    S = 0 := by
  cases S with
  | zero => rw [← Point.zero_def]
  | some x y h =>
      exfalso
      rw [pointDivisorAff_some, Finsupp.smul_single, smul_eq_mul, mul_one] at hfdiv
      obtain ⟨x₂, y₂, h₂, hmem, hne⟩ :=
        exists_torsion_two_weilPairingElt_ne_one h2 h hf hfdiv hgS hu
      exact hne (hone x₂ y₂ h₂ hmem)

end Nondegenerate

/-! ### Non-vacuity

Everything above carries `[IsAlgClosed F]` and `[W.IsElliptic]`, and the headline additionally needs
a nonsingular affine `2`-torsion point.  `y² = x³ − x` over `AlgebraicClosure ℚ` supplies all three
with the torsion point **named**: it is `(0, 0)`.  This is the curve `#758`/`#759`/`#763`/`#774`/
`#791` all use, for the same reason — the `ℚ` curve of the rest of `FunctionField/` cannot witness a
statement needing an algebraically closed base. -/

section Nonvacuity

/-! The certificate curve `y² = x³ − x` is the shared `EllipticCurves.Fixture.y2EqX3SubX`, and the
base — algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here. -/

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

/-- `S = (0, 0)` lies on `y² = x³ − x` and is nonsingular. -/
private lemma exampleNonsingular : (y2EqX3SubX AlgClosedQ).Nonsingular 0 0 :=
  (y2EqX3SubX AlgClosedQ).equation_iff_nonsingular.mp (by
    norm_num [y2EqX3SubX, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `S = (0, 0)` is `2`-torsion: `2y + a₁x + a₃ = 0` reads `0 = 0`. -/
private lemma exampleTorsion :
    Point.some (0 : AlgClosedQ) 0 exampleNonsingular ∈ (y2EqX3SubX AlgClosedQ).torsion 2 :=
  (mem_torsion_two_some_iff exampleNonsingular).mpr (by norm_num [y2EqX3SubX])

open Classical in
/-- **Non-degeneracy at `n = 2`, on a curve that exists**, with the `2`-torsion point named. -/
example : ∃ f : (y2EqX3SubX AlgClosedQ).FunctionField, f ≠ 0 ∧
    (y2EqX3SubX AlgClosedQ).divisor f
      = Finsupp.single (pointClosedPoint exampleNonsingular.left) (2 : ℤ) ∧
    ∃ gS : (y2EqX3SubX AlgClosedQ).FunctionField, gS ≠ 0 ∧
      (∃ u : (y2EqX3SubX AlgClosedQ).CoordinateRingˣ,
        (u : (y2EqX3SubX AlgClosedQ).CoordinateRing) • gS ^ 2 = mulByTwoEndo exampleTwo f) ∧
      ∃ (x₂ y₂ : AlgClosedQ) (h₂ : (y2EqX3SubX AlgClosedQ).Nonsingular x₂ y₂),
        Point.some x₂ y₂ h₂ ∈ (y2EqX3SubX AlgClosedQ).torsion 2 ∧
          weilPairingElt h₂.left gS ≠ 1 :=
  exists_gS_two_weilPairingElt_ne_one exampleTwo exampleNonsingular exampleTorsion

end Nonvacuity

end WeierstrassCurve.Affine
