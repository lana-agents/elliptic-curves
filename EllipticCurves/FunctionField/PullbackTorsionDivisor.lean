/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.PullbackDivisor

/-!
# Naming the quotient divisor: `div (f_S ∘ [2]) = n • [2]∗((S) − (O))`

`EllipticCurves.FunctionField.PlacePullback` ends with `dvd_divisorProj_mulByTwoEndo_of_torsion`:
for an `n`-torsion point `S`, `n` divides **every** coefficient of `div (f_S ∘ [2])`.  The quotient
divisor is left anonymous there, because at that point in the tree `[2]∗` exists only pointwise.
`EllipticCurves.FunctionField.PullbackDivisor` turns it into a map of divisors, and that is all it
takes to name the quotient:

```lean
divisorProj W (mulByTwoEndo h2 f_S)
    = (n : ℤ) • pullbackDivisorTwo h2 ((S) − (O)).
```

No new geometry and no new value of `ramificationIdx`: `divisorProj W f_S = n·(S) − n·(O)` is the
merged `divisorProj_eq_single_sub_single_of_torsion`, `pullbackDivisorTwo` is an `AddMonoidHom`, so
it commutes with `(n : ℤ) • ·`, and `divisorProj_mulByTwoEndo` moves the pullback across.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.pullbackDivisorTwo_zsmul` — `[2]∗` is `ℤ`-linear;
* **`WeierstrassCurve.Affine.CoordinateRing.divisorProj_mulByTwoEndo_of_torsion`** — the named
  quotient, in the same `∃ f, …` shape as `dvd_divisorProj_mulByTwoEndo_of_torsion` so the two can
  be read side by side;
* `WeierstrassCurve.Affine.CoordinateRing.dvd_divisorProj_mulByTwoEndo_of_torsion'` — `#668`'s
  divisibility corollary re-derived from the named form in one line, which is the check that the
  new statement is strictly stronger and that nothing drifted.

## What remains for `#418`

Rung 5 (`#418`, the `n`-th root `g_S` with `g_S^n = c·(f_S ∘ [n])`) is blocked on a hypothesis its
two approved PRs carry abstractly and call `hprin`:

```
hprin : ∃ g₀ ≠ 0, n • divisor W g₀ = divisor W (mulByTwoEndo h2 f_S)
```

— "the divisor `D` with `n · D = div (f_S ∘ [2])` is **principal**".  That is genuinely gated:
`n · D` principal does *not* imply `D` principal, and the failure is exactly the `n`-torsion of the
class group that the Weil pairing measures.

What is *not* gated is knowing **which** divisor `D` is, and after this file it has a name.  The
remaining content of `#418` is one sentence about a named divisor:

> `[2]∗((S) − (O))` is principal.

### What gates that sentence — and it is not Ward (`#765`)

⚠️ An earlier version of this section said discharging `hprin` is "Ward-coupled (`#E[n] = n²`,
`#242`)".  **That is false at the `n` rung 5 is stated at.**  `card_torsion_two` and
`card_torsion_three` are merged (`Torsion/TwoTorsion`, `Torsion/ThreeTorsionStructure`) and neither
goes through Ward; Ward gates `#E[n] = n²` at *general* `n` only.  The class-group layer is merged
too — `classOfDivisor` and `exists_divisor_eq_iff_classOfDivisor_eq_one` (`DivisorPrincipality`,
`#726`).

⚠️ Earlier wording said the **fibre description** `[2]∗((S) − (O)) = ∑_{R ∈ E[2]} ((P ⊕ R) − (R))`
is what is missing, and placed it at `#639` rung 8 (`#701` and its children).  The placement was
wrong — `#701` is the fundamental identity, which counts the fibre without describing it — and the
description itself is now **merged**, at rung 9: `EllipticCurves.FunctionField.MulByTwoFibreAffine`
(`#774`) proves `comapProjPointTwo (projPointOfPoint P) = projPointOfPoint (2 • P)`, identifies each
fibre with the coset `{ P ⊕ R : R ∈ E[2] }`, and pins every `ramificationIdxTwo` over a rational
point to `1`.  `#755`'s `nonempty_fibre_comapProjPointTwo` and `#763`'s count were its inputs.

What is left of `hprin` at `n = 2` is the class-group computation
`∑_R toClass (P ⊕ R) − ∑_R toClass R = 4 · toClass P = toClass ([2]S) = 0`; this file does not do
it either.

### The chart mismatch is *not* a second gate (`#765`)

An earlier version of this section warned that `hprin` is stated with the **affine** `divisor W`
while everything here is `divisorProj` on `ProjPoint W`, and left open whether that is an
independent obstruction.  It is not, and the reason is worth stating so nobody prices it twice.

The direction needed is projective ⟹ affine, which is the free one:
`divisorProj_apply_some : divisorProj W f (some v) = divisor W f v` is unconditional, so evaluating
`divisorProj_mulByTwoEndo_of_torsion` at `some w` and reading off `pullbackDivisorTwo_apply` (an
`rfl` lemma) gives, for every affine place `w` and with no new input,

```
divisor W (f_S ∘ [2]) w = n * (ramificationIdxTwo h2 (some w) * D (comapProjPointTwo h2 (some w))).
```

The `−n·(O)` term drops out because `Finsupp.single none _` vanishes at `some w` — and `hprin` is
an affine statement to begin with, so nothing it needs is lost.

⚠️ What does **not** transfer is the named lemma
`divisor_eq_single_of_divisorProj_eq_single_sub_single` (`WeilPairingAlternatingTwo`).  Its
hypothesis pins the projective divisor to the two-point shape `single (some v) n - single none n`,
and `n • pullbackDivisorTwo ((S) − (O))` is supported on the whole `[2]`-fibre over both points.
Only its *proof step* generalises, and that step is the one line above.

So there was **one** gate on `hprin`, not two: the fibre description — and as of `#774` that gate
is merged.  This file still does not discharge `hprin`; the chart was never why, and what is left
is the class-group computation above.

## What is *not* here

* Any attempt to discharge principality.  See above: what is left of it is the class-group
  computation, the fibre description having landed with `#774`.
* Any restatement of rung 5's `exists_gS_two` / `exists_gS_three` in projective terms.  That is a
  change to merged rung-5 code and needs its own issue.
* The degree formula, values of `ramificationIdx`, `[3]∗`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.
-/

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]

/-- **`[2]∗` is `ℤ`-linear on divisors.**  It is an `AddMonoidHom`, so this is `map_zsmul`; it is
named because the statement below is exactly an application of it. -/
theorem pullbackDivisorTwo_zsmul (h2 : (2 : F) ≠ 0) (n : ℤ) (D : ProjPoint W →₀ ℤ) :
    pullbackDivisorTwo h2 (n • D) = n • pullbackDivisorTwo h2 D :=
  map_zsmul _ _ _

/-- **The quotient divisor, named.**  For an `n`-torsion point `S = (x, y)` the merged
`divisorProj_eq_single_sub_single_of_torsion` supplies `f_S` with `div f_S = n·(S) − n·(O)`, and
then

```
div (f_S ∘ [2]) = n • [2]∗((S) − (O)).
```

The `∃ f, …` shape and the middle conjunct are those of
`dvd_divisorProj_mulByTwoEndo_of_torsion` (`PlacePullback`), so the two statements are directly
comparable: this one replaces "`n` divides every coefficient" by an equation naming the quotient.

Nothing here computes a ramification index — `[2]∗((S) − (O))` is as abstract as
`pullbackDivisorTwo` is. -/
theorem divisorProj_mulByTwoEndo_of_torsion [DecidableEq F] (h2 : (2 : F) ≠ 0) {x y : F}
    (h : W.Nonsingular x y) {n : ℕ} (hP : Point.some x y h ∈ W.torsion n) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
        - Finsupp.single none (n : ℤ) ∧
      divisorProj W (mulByTwoEndo h2 f)
        = (n : ℤ) • pullbackDivisorTwo h2 (Finsupp.single (some (pointClosedPoint h.left)) (1 : ℤ)
            - Finsupp.single (none : ProjPoint W) (1 : ℤ)) := by
  classical
  obtain ⟨f, hf, hdiv⟩ := divisorProj_eq_single_sub_single_of_torsion h hP
  refine ⟨f, hf, hdiv, ?_⟩
  have hsmul : divisorProj W f
      = (n : ℤ) • (Finsupp.single (some (pointClosedPoint h.left)) (1 : ℤ)
          - Finsupp.single (none : ProjPoint W) (1 : ℤ)) := by
    rw [hdiv, smul_sub, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [divisorProj_mulByTwoEndo h2 hf, hsmul, pullbackDivisorTwo_zsmul]

/-- **`#668`'s divisibility corollary, re-derived from the named quotient.**  `Dvd.intro` applied
to the equation above: every coefficient of `div (f_S ∘ [2])` is `n` times the corresponding
coefficient of `[2]∗((S) − (O))`.

The primed name is deliberate — `dvd_divisorProj_mulByTwoEndo_of_torsion` in `PlacePullback` is the
same statement proved without `pullbackDivisor`, and keeping both is the check that naming the
quotient lost nothing. -/
theorem dvd_divisorProj_mulByTwoEndo_of_torsion' [DecidableEq F] (h2 : (2 : F) ≠ 0) {x y : F}
    (h : W.Nonsingular x y) {n : ℕ} (hP : Point.some x y h ∈ W.torsion n) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
        - Finsupp.single none (n : ℤ) ∧
      ∀ p : ProjPoint W, (n : ℤ) ∣ divisorProj W (mulByTwoEndo h2 f) p := by
  classical
  obtain ⟨f, hf, hdiv, heq⟩ := divisorProj_mulByTwoEndo_of_torsion h2 h hP
  refine ⟨f, hf, hdiv, fun p => ?_⟩
  rw [heq, Finsupp.smul_apply, smul_eq_mul]
  exact Dvd.intro _ rfl

/-! ### Non-vacuity

`pullbackDivisorTwo` is built from a choice principle and everything above is stated under
`[IsDedekindDomain W.CoordinateRing]`, so it is worth exhibiting a curve where the instances are
discharged.  `y² = x³ - x` over `ℚ` has discriminant `64`, and `IsElliptic` alone gives the
Dedekind instance. -/

section Nonvacuity

/-- The curve `y² = x³ - x` over `ℚ`, of discriminant `64`. -/
private def exampleCurve : Affine ℚ := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

example : IsDedekindDomain exampleCurve.CoordinateRing := inferInstance

example (n : ℤ) (D : ProjPoint exampleCurve →₀ ℤ) :
    pullbackDivisorTwo (W := exampleCurve) (by norm_num) (n • D)
      = n • pullbackDivisorTwo (W := exampleCurve) (by norm_num) D :=
  pullbackDivisorTwo_zsmul _ n D

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
