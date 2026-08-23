/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.CoordinateRingUnits
import EllipticCurves.FunctionField.DivisorConstant
import EllipticCurves.FunctionField.MulByThreeGalois
import EllipticCurves.FunctionField.PullbackPrincipalityThree
import EllipticCurves.FunctionField.WeilPairingAlternating

/-!
# Non-degeneracy of the Weil pairing at `n = 3` over an algebraically closed field

Silverman *AEC* III.8, Prop. 8.1(d): if `e_n(S, T) = 1` for every `T ∈ E[n]` then `S = O`.

This is the `n = 3` mirror of `EllipticCurves.FunctionField.WeilPairingNondegenerateTwo`, whose
scope note has tracked the gap through five merges.  Every one of the seven steps that file
enumerates has an `n = 3` counterpart, and as of `#825` every counterpart is merged; what did not
exist was the assembly.  **Nothing new is proved here about curves.**

## The seven steps at `n = 3`

Let `S = (x, y)` be a nonsingular *affine* `3`-torsion point.  Affine means `S ≠ O`
(`Point.some_ne_zero`), which is the whole content of the conclusion `S = O`, contraposed.

1. **Rung 5, unconditionally.**  `exists_gS_three_of_isAlgClosed` (`PullbackPrincipalityThree`,
   `#825`) supplies `f_S ≠ 0` with `div f_S = 3·(S)` and `g_S ≠ 0` with `u · g_S ^ 3 = [3]∗ f_S`.
2. **`e_3(S, T) = 1` *is* translation-invariance of `g_S`** —
   `weilPairingElt_eq_one_iff_translateEndo_fixed` (`WeilPairingAlternating`).  ⚠️ This lemma
   never mentions `n`: it is `τ_T∗ g / g = 1 ↔ τ_T∗ g = g` and nothing more.
3. **Invariance under every `T ∈ E[3]` is membership in `Fixed(E[3])`** — `mem_fixedFieldThree_iff`
   is `Iff.rfl`, and `torsionThreeMul_smul_def` / `translateAut_apply_some`
   (`TranslationActionThree`, `TranslationAction`) reduce the action to `translateEndo` by a case
   split on `W.Point`.  The point at infinity acts as the identity, so it carries no information —
   see the warning below.
4. **`Fixed(E[3]) = [3]∗F(W)`** — `fixedFieldThree_eq_mulByThreeFieldRange` (`MulByThreeGalois`,
   `#784`), Artin against `card_torsionThreeMul` (`#783`) on one side and
   `finrank_mulByThreeFieldRange` (`#775`) on the other.  So `g_S = [3]∗ q` for some `q`.
5. **Cancelling `[3]∗`.**  The unit `u` is a constant (`exists_eq_algebraMap_of_isUnit`), `[3]∗`
   fixes constants (`mulByThreeEndo_algebraMap_base`) and is injective, so `c · q ^ 3 = f_S`.
6. **Divisors.**  `divisor_mul`, `divisor_algebraMap_base` and `divisor_pow` give
   `3 • div q = 3·(S)`, hence `div q = (S)` after cancelling `3` place by place.
7. **The contradiction.**  `not_exists_divisor_eq_single_pointClosedPoint` (`DivisorPrincipality`,
   `#726`): a single affine rational point is never a principal divisor.  This is the only step of
   the seven that *rules a function out* rather than exhibiting one, and it is the one step that is
   completely `n`-free.

## Main statements

* `WeierstrassCurve.Affine.not_forall_torsionThreeMul_smul_eq` — the core, stated against an
  arbitrary rung-5 root rather than against `#825`'s existential: a `g_S` with
  `u · g_S ^ 3 = [3]∗ f_S` over `div f_S = 3·(S)` is **not** fixed by all of `E[3]`.
* `WeierstrassCurve.Affine.exists_torsion_three_weilPairingElt_ne_one` — the same in pairing
  language: some affine `T ∈ E[3]` has `e_3(S, T) ≠ 1`.
* `WeierstrassCurve.Affine.exists_gS_three_weilPairingElt_ne_one` — rung 5 and non-degeneracy
  together, with no hypothesis beyond the setting.
* **`WeierstrassCurve.Affine.eq_zero_of_forall_weilPairingElt_eq_one_three`** — Silverman's own
  shape: for `f_S` with `div f_S = 3 · pointDivisorAff S` and a cube root `g_S` of `[3]∗ f_S` up to
  a unit, `e_3(S, ·) ≡ 1` on `E[3]` forces `S = O`.

⚠️ **The witness `T` is necessarily affine.**  At `T = O` the translation is the identity
(`translateAut_zero`) and `e_3(S, O) = 1` for trivial reasons, so a statement asserting
`∃ T ∈ E[3], e_3(S, T) ≠ 1` with `T` ranging over `W.Point` would still be true but a statement
proving it *at* `O` would be false.  Every conclusion below names an affine `T` by giving its
coordinates.  This is the `n = 2` file's warning and it transposes without change.

## Scope

⚠️ **`h2` and `h3` are both needed, and the `n = 2` file's `h2` is not the same `h2`.**  At `n = 2`
the single hypothesis `(2 : F) ≠ 0` is what makes `[2]∗` exist.  Here `h3` is what makes `[3]∗`
exist, and `h2` enters *separately*, twice: through the doubling slope inside
`PullbackPrincipalityThree`'s producer, and through `finite_torsionThreeMul` /
`card_torsionThreeMul`, which `fixedFieldThree_eq_mulByThreeFieldRange` runs on.  Neither
occurrence is removable by restating anything here.

⚠️ **`[IsAlgClosed F]` is load-bearing and enters twice, independently** — through step 1 (`#825`,
itself through the surjectivity of `[3]` on points and `#819`'s fibre description) and through
step 4 (`#784`, via `card_torsion_three`).  This is the same two-fold entry the `n = 2` file
records, with `#791`/`#759` replaced by `#825`/`#784`.

⚠️ **The count that enters is `9`, and it enters as `card_torsionThreeMul`, not as a literal.**
`#819` recorded that the `n = 3` fibre count is reached as a coset of `E[3]` rather than one point
per root of a division polynomial; that distinction lives entirely inside `#784`/`#825` and is
invisible here, exactly as `|E[2]| = 4` is invisible in the `n = 2` file.  Nothing below consumes a
number.

⚠️ **The statements below are pinned to `Classical.propDecidable`.**  `open Classical in` is
required and not a formality: `TorsionThreeMul` bakes the classical `DecidableEq F` instance in,
and the statements mention `W.torsion 3`.  A consumer whose own variable block carries
`[DecidableEq F]` bridges with
`obtain rfl : ‹DecidableEq F› = (fun a b => Classical.propDecidable (a = b)) :=
Subsingleton.elim _ _`.

⚠️ **This is not bilinearity, not the alternating property (`#465`, assembled at `n = 3` in
`WeilPairingAlternatingThreeAlgClosed`), not Galois-equivariance (`#456`, assembled at `n = 3` in
`WeilPairingGaloisRoot`), and not general `n`.**  It says nothing about `#E[n] = n²` at general `n`
(`#242`, `#404`, Ward): it is Ward-free for the same reason the `n = 2` file is.

⚠️ **There is no `W.Point`-level pairing in this tree**, so "non-degeneracy" cannot be stated as a
property of a bilinear map.  `eq_zero_of_forall_weilPairingElt_eq_one_three` is as close to
Silverman's sentence as the current packaging allows: it quantifies over the *data* `f_S`, `g_S`
that rung 5 produces.  Inventing a fifth spelling of the pairing here would be the drift this front
keeps paying for.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8, Prop. 8.1(d).
-/

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

section Nondegenerate

variable [W.IsElliptic] [IsAlgClosed F] {x y : F}

open Classical in
/-- **The core of non-degeneracy at `n = 3`: a rung-5 root of `f_S` is not `E[3]`-invariant.**

Given a nonsingular affine point `S = (x, y)`, a nonzero `f` with `div f = 3·(S)`, and a `g_S` with
`u · g_S ^ 3 = [3]∗ f` for a unit `u` of `F[W]`, the translation action of `E[3]` does **not** fix
`g_S`.

Were it to, `g_S` would lie in `Fixed(E[3]) = [3]∗F(W)`
(`fixedFieldThree_eq_mulByThreeFieldRange`, `#784`), say `g_S = [3]∗ q`; the unit `u` is a constant
`c` (`exists_eq_algebraMap_of_isUnit`), `[3]∗` fixes constants and is injective, so `c · q ^ 3 = f`
and therefore `3 • div q = 3·(S)`.  Cancelling `3` place by place gives `div q = (S)`, and a single
affine rational point is never a principal divisor
(`not_exists_divisor_eq_single_pointClosedPoint`, `#726`).

Stated against an arbitrary rung-5 root rather than against `exists_gS_three_of_isAlgClosed`'s
existential, so that it applies to *any* function with the rung-5 property; `g_S ≠ 0` is not needed
here (it follows from `f ≠ 0`) and is not assumed. -/
theorem not_forall_torsionThreeMul_smul_eq (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h : W.Nonsingular x y) {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ))
    {u : W.CoordinateRingˣ}
    (hu : (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f) :
    ¬ ∀ T : TorsionThreeMul W, T • gS = gS := by
  classical
  intro hfix
  -- Steps 3 and 4: `g_S ∈ Fixed(E[3]) = [3]∗F(W)`.
  have hmem : gS ∈ fixedFieldThree W := mem_fixedFieldThree_iff.mpr hfix
  rw [← fixedFieldThree_eq_mulByThreeFieldRange h2 h3] at hmem
  obtain ⟨q, hq⟩ := hmem
  have hq' : mulByThreeEndo h2 h3 q = gS := hq
  clear hq
  -- Step 5: the unit is a constant, and `[3]∗` cancels.
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_isUnit u.isUnit
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact u.ne_zero (by rw [hc, map_zero])
  have hstep : algebraMap F W.FunctionField c * gS ^ 3 = mulByThreeEndo h2 h3 f := by
    rw [← hu, Algebra.smul_def, hc, ← IsScalarTower.algebraMap_apply]
  have hpull : mulByThreeEndo h2 h3 (algebraMap F W.FunctionField c * q ^ 3)
      = mulByThreeEndo h2 h3 f := by
    rw [map_mul, map_pow, mulByThreeEndo_algebraMap_base, hq', hstep]
  have heq : algebraMap F W.FunctionField c * q ^ 3 = f := (mulByThreeEndo h2 h3).injective hpull
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hf (by rw [← heq]; ring)
  have hcne : algebraMap F W.FunctionField c ≠ 0 := by simpa using hc0
  -- Step 6: `3 • div q = 3·(S)`, and `3` cancels place by place.
  have hdiv : (3 : ℕ) • divisor W q = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) := by
    rw [← hfdiv, ← heq, divisor_mul hcne (pow_ne_zero 3 hq0), divisor_algebraMap_base hc0,
      zero_add, divisor_pow]
  have hsingle : divisor W q = Finsupp.single (pointClosedPoint h.left) (1 : ℤ) := by
    ext v
    have hv := DFunLike.congr_fun hdiv v
    rw [Finsupp.smul_apply, nsmul_eq_mul] at hv
    push_cast at hv
    refine mul_left_cancel₀ (a := (3 : ℤ)) (by norm_num) ?_
    rw [hv, Finsupp.single_apply, Finsupp.single_apply]
    split <;> norm_num
  -- Step 7: a single affine rational point is never principal.
  exact not_exists_divisor_eq_single_pointClosedPoint h ⟨q, hq0, hsingle⟩

open Classical in
/-- **Non-degeneracy at `n = 3`, in pairing language**: some affine `T ∈ E[3]` has
`e_3(S, T) ≠ 1`.

Step 2 (`weilPairingElt_eq_one_iff_translateEndo_fixed`) turns each `e_3(S, T) = 1` into
`τ_T∗ g_S = g_S`, and step 3 assembles those into invariance under the whole action — the point at
infinity contributing nothing, since `translateAut 0` is the identity.  So a `g_S` pairing trivially
with every affine `3`-torsion point would be `E[3]`-invariant, which
`not_forall_torsionThreeMul_smul_eq` forbids.

⚠️ The witness is produced with its coordinates because it must be **affine**: `weilPairingElt` is
indexed by an `Equation`, and at `T = O` the element is `1` for trivial reasons. -/
theorem exists_torsion_three_weilPairingElt_ne_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h : W.Nonsingular x y) {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ))
    (hgS : gS ≠ 0) {u : W.CoordinateRingˣ}
    (hu : (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f) :
    ∃ (x₃ y₃ : F) (h₃ : W.Nonsingular x₃ y₃), Point.some x₃ y₃ h₃ ∈ W.torsion 3 ∧
      weilPairingElt h₃.left gS ≠ 1 := by
  classical
  by_contra hall
  push Not at hall
  refine not_forall_torsionThreeMul_smul_eq h2 h3 h hf hfdiv hu fun T => ?_
  rw [torsionThreeMul_smul_def]
  have hmem : (T.toAdd : W.Point) ∈ W.torsion 3 := T.toAdd.2
  set P : W.Point := (T.toAdd : W.Point) with hP
  clear_value P
  cases P with
  | zero => rw [← Point.zero_def, translateAut_zero]; rfl
  | some x₃ y₃ h₃ =>
      rw [translateAut_apply_some]
      exact (weilPairingElt_eq_one_iff_translateEndo_fixed h₃.left hgS).mp (hall _ _ h₃ hmem)

open Classical in
/-- **Rung 5 and non-degeneracy together, with nothing carried**: for a nonsingular affine
`3`-torsion point `S` over an algebraically closed field of characteristic `≠ 2, 3` there are a
principal function `f_S` with `div f_S = 3·(S)`, a nonzero `g_S` with `u · g_S ^ 3 = [3]∗ f_S`, and
an **affine** `T ∈ E[3]` with `e_3(S, T) ≠ 1`.

This is the statement that could not be made before `#825`: its rung-5 half is
`exists_gS_three_of_isAlgClosed`, which is `exists_gS_three` with `hprin` discharged. -/
theorem exists_gS_three_weilPairingElt_ne_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion 3) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f) ∧
        ∃ (x₃ y₃ : F) (h₃ : W.Nonsingular x₃ y₃), Point.some x₃ y₃ h₃ ∈ W.torsion 3 ∧
          weilPairingElt h₃.left gS ≠ 1 := by
  obtain ⟨f, hf, hfdiv, gS, hgS, u, hu⟩ := exists_gS_three_of_isAlgClosed h2 h3 h hS
  exact ⟨f, hf, hfdiv, gS, hgS, ⟨u, hu⟩,
    exists_torsion_three_weilPairingElt_ne_one h2 h3 h hf hfdiv hgS hu⟩

open Classical in
/-- **Silverman III.8.1(d) at `n = 3`: `e_3(S, ·) ≡ 1` forces `S = O`.**

`S : W.Point` is arbitrary — no torsion hypothesis is needed, because the torsion of `S` is what
produces `f_S` and `g_S` in the first place and those are hypotheses here.  The divisor condition is
written with `#791`'s `pointDivisorAff`, which is defined uniformly on `W.Point` and sends `O` to
`0`, so no case split appears in the statement: at an affine `S` it reads `div f_S = 3·(S)`, and at
`S = O` it reads `div f_S = 0`, where the conclusion holds anyway.  ⚠️ `pointDivisorAff` is `n`-free
and is reused from the `n = 2` line unchanged; only the scalar in front of it moves.

⚠️ The trivial-pairing hypothesis quantifies over **affine** `3`-torsion points, which is not a
restriction: `e_3(S, O) = 1` always. -/
theorem eq_zero_of_forall_weilPairingElt_eq_one_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {S : W.Point} {f gS : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = (3 : ℤ) • pointDivisorAff W S) (hgS : gS ≠ 0)
    {u : W.CoordinateRingˣ} (hu : (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f)
    (hone : ∀ (x₃ y₃ : F) (h₃ : W.Nonsingular x₃ y₃), Point.some x₃ y₃ h₃ ∈ W.torsion 3 →
      weilPairingElt h₃.left gS = 1) :
    S = 0 := by
  cases S with
  | zero => rw [← Point.zero_def]
  | some x y h =>
      exfalso
      rw [pointDivisorAff_some, Finsupp.smul_single, smul_eq_mul, mul_one] at hfdiv
      obtain ⟨x₃, y₃, h₃, hmem, hne⟩ :=
        exists_torsion_three_weilPairingElt_ne_one h2 h3 h hf hfdiv hgS hu
      exact hne (hone x₃ y₃ h₃ hmem)

end Nondegenerate

/-! ### Non-vacuity

Everything above carries `[IsAlgClosed F]` and `[W.IsElliptic]`, and the headline additionally needs
a nonsingular affine `3`-torsion point.  `y² + y = x³` over `AlgebraicClosure ℚ` supplies all three
with the torsion point **named**: it is `(0, 0)`, because `Ψ₃ = 3X⁴ + 3b₆X = 3X(X³ + 1)` here.

⚠️ The `n = 2` file's certificate curve `y² = x³ − x` would **not** serve: its
`Ψ₃ = 3X⁴ − 6X² − 1` has no rational root, so none of its nine `3`-torsion points over
`AlgebraicClosure ℚ` can be named without a genuine algebraic-number argument.  Two independent
`n = 3` fronts (`#830`, `#829`) hit this before this file did; a second base curve is intrinsic to
every `n = 3` mirror of an `n = 2` theorem with a committed non-vacuity example, not a stylistic
choice. -/

section Nonvacuity

/-- An algebraically closed field of characteristic zero. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

/-- The curve `y² + y = x³` over `AlgebraicClosure ℚ`, of discriminant `−27`. -/
private noncomputable def exampleCurveThree : Affine exampleField := ⟨0, 0, 1, 0, 0⟩

private instance : exampleCurveThree.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurveThree, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleTwo : (2 : exampleField) ≠ 0 := by norm_num

private lemma exampleThree : (3 : exampleField) ≠ 0 := by norm_num

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
/-- **Non-degeneracy at `n = 3`, on a curve that exists**, with the `3`-torsion point named. -/
example : ∃ f : exampleCurveThree.FunctionField, f ≠ 0 ∧
    exampleCurveThree.divisor f
      = Finsupp.single (pointClosedPoint exampleNonsingularThree.left) (3 : ℤ) ∧
    ∃ gS : exampleCurveThree.FunctionField, gS ≠ 0 ∧
      (∃ u : exampleCurveThree.CoordinateRingˣ,
        (u : exampleCurveThree.CoordinateRing) • gS ^ 3
          = mulByThreeEndo exampleTwo exampleThree f) ∧
      ∃ (x₃ y₃ : exampleField) (h₃ : exampleCurveThree.Nonsingular x₃ y₃),
        Point.some x₃ y₃ h₃ ∈ exampleCurveThree.torsion 3 ∧
          weilPairingElt h₃.left gS ≠ 1 :=
  exists_gS_three_weilPairingElt_ne_one exampleTwo exampleThree exampleNonsingularThree
    exampleTorsionThree

end Nonvacuity

end WeierstrassCurve.Affine
