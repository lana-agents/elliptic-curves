/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByThreeRamification
import EllipticCurves.FunctionField.MulByTwoFibreAffine
import EllipticCurves.Torsion.TriplingCoords

/-!
# The place contraction of `[3]` **is** tripling, and the fibre over a rational point

`#814` (`EllipticCurves.FunctionField.MulByThreePlacePullback`) built the `[3]∗` place calculus and
computed it at `O`; `#815` (`EllipticCurves.FunctionField.MulByThreeRamification`) proved the
arithmetic `∑_{p ↦ q} e_p = 9`.  Neither computed a single value of `comapProjPointThree` at an
affine place.  This file computes them all:

```
comapProjPointThree h2 h3 (projPointOfPoint P) = projPointOfPoint (3 • P)
```

for **every** `P : W.Point`, with no case hypothesis — the `n = 3` mirror of `#774`
(`MulByTwoFibreInfinity` together with `MulByTwoFibreAffine`), and the last geometric rung below
`hprin` at `n = 3` (`#418`), which is discharged on top of it in
`EllipticCurves.FunctionField.PullbackPrincipalityThree`.

From it, over an algebraically closed base field: the fibre over any rational point is the coset
`{ P ⊕ R : R ∈ E[3] }`, it has exactly nine elements, every ramification index on it is `1`, and

```
[3]∗(S) = ∑_{p ↦ S} (p) = ∑_{R ∈ E[3]} (P ⊕ R)   for any P with 3 • P = S.
```

## The crux was a transcription after all — and two merged files said it was not

`#818`'s tree-wide audit, written an hour before this file, put the following into
`MulByTwoFibreAffine`'s scope note — and this file's diff is what replaces it there:
`mulByThreeCoordHom_XClass`/`_YClass` do not exist, nobody has scouted whether the `[3]` version of
the ideal computation has the same shape, and it must not be priced as a transcription.

That caution was right to be stated and turns out to be false in fact.  The four-step `n = 2`
argument transposes with one change, and the change makes the `[3]` version **easier**, not harder:

1. `[3]∗` on the two generators — `mulByThreeCoordHom_XClass`/`_YClass` below, the `n = 2` proofs
   verbatim over `mulByThreeEndo_algebraMap`.
2. Each vanishes at `P`.  ⚠️ **This is the step that came out cheaper.**  At `n = 2` the numerator
   is `Φ₂ − C x₂ · Ψ₂Sq` with `x₂ = addX x x (slope x x y y)`, and proving it vanishes at `P` *is*
   the duplication formula `addX_self_mul_Ψ₂Sq_eval`.  Here the statement is made about the
   **division form** `Φ₃(x)/ΨSq₃(x)` directly, so the vanishing is `field_simp` and the tripling
   formula is not needed at all.  `EllipticCurves.Torsion.TriplingCoords` enters one layer up,
   where the closed point of `(Φ₃/ΨSq₃, ω₃/(2 ψ₃³))` has to be identified with the closed point of
   `3 • P` — which is what it says.
3. `divisorProj_mulByThreeEndo_apply` with `e_p > 0` transports "vanishes at `P`" across the
   contraction.
4. The contracted prime then contains the maximal `ker (evalEvalHom h₃)` and therefore is it.

> ⚠️ **The moral, and it is the fourth instance on this front.**  `DoublingCoords`, `#811` and
> `#815` each found an `n = 3` rung priced as research that was not.  Here the prose was *"not
> scouted"* rather than *"blocked"*, which is the honest form — and the scouting still cost less
> than writing the sentence.  Type-check the transposition in a scratch file before pricing it.

## The `2`-torsion case is new at `n = 3`, and it is discharged here

At `n = 2` the coordinate formula excludes exactly the kernel, so `MulByTwoFibreAffine` has one
excluded family and `MulByTwoFibreInfinity` handles it.  At `n = 3` **two** families are outside
`TriplingCoords`'s hypotheses, and they are different from each other:

* `Ψ₃(x) = 0` — the kernel.  Handled below by
  `comapProjPointThree_pointClosedPoint_of_eval_Ψ₃_eq_zero`, the mirror of
  `MulByTwoFibreInfinity`'s step 1: at a root of `Ψ₃` the denominator `ΨSq₃` of
  `x ∘ [3]` vanishes and the numerator does not (`isCoprime_Φ_three_ΨSq_three`, `#682`'s `n = 3`
  analogue, merged), so `x ∘ [3]` has a pole and the contraction cannot be affine.
* `y = negY x y` — the `2`-torsion, which at `n = 2` **is** the kernel and so has no `n = 2`
  analogue at all.  `TriplingCoords` cannot reach it: its route to `3 • P` goes through the doubling
  step, whose tangent slope is undefined there.  But the crux does not need `TriplingCoords`, and
  what is left is arithmetic: for such a `P`, `Ψ₂Sq(x) = (2y + a₁x + a₃)² = 0`, so
  `Φ₃ = x·Ψ₃² − preΨ₄·Ψ₂Sq` collapses to `x·ΨSq₃` and `ω₃` collapses to `2y·ψ₃³` — the tripling
  coordinates *are* `(x, y)`, which is right, since `3 • P = P + 2 • P = P`.  That is
  `tripling_eq_self_of_Y_eq` and `omegaThree_div_eq_self_of_Y_eq` below.

⚠️ And the two families do not overlap: `Ψ₃` and `Ψ₂Sq` are coprime on an elliptic curve
(`isCoprime_Ψ₃_Ψ₂Sq`), so a `3`-torsion point is never `2`-torsion — `Y_ne_negY_of_eval_Ψ₃_eq_zero`.
That is the Lean form of "an affine point cannot be both", and it is what lets the uniform statement
close with no gap.

## Why this file imports the `[2]` one

`MulByTwoFibreAffine` proves `ord_genPsi_pos_iff`, `ord_genPsi_eq_zero`,
`ord_pos_of_eq_evalEval_div`, and defines `projPointOfPoint` with `projPointOfPoint_zero`,
`projPointOfPoint_some` and `projPointOfPoint_injective`.  All seven are **`[2]`-free**: facts about
closed points, about fractions of coordinate functions, and about the rational locus of
`ProjPoint W`, with no doubling in any of them.  They are consumed unchanged rather than re-proved.

⚠️ Moving them to an earlier module would be tidier and is **deliberately not done**: it edits a
merged file for no mathematical gain.  `EllipticCurves.Torsion.TriplingCoords`,
`EllipticCurves.Torsion.DoublingCoords` and `EllipticCurves.FunctionField.MulByThreePlacePullback`
each declined the same trade, for the same reason.

## The count, which does *not* transpose from `n = 2`

At `n = 2` the fibre over `O` is `{O}` together with one point per root of `Ψ₂Sq` — one, because
negation **fixes** the `2`-torsion points — giving `1 + 3 = 4`.  A `3`-torsion point is not
`2`-torsion, so each of the four roots of `Ψ₃` carries **two** points and the count is
`1 + 2·4 = 9`.
Nothing below counts roots, though: the fibre is obtained as a coset of `E[3]` and its cardinality
from `card_torsion_three`, so the asymmetry is absorbed by the group-theoretic argument rather than
met head-on.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.mulByThreeCoordHom_XClass` and `mulByThreeCoordHom_YClass`
  — `[3]∗(X − x₃) = x∘[3] − x₃` and `[3]∗(Y − y₃) = y∘[3] − y₃`;
* `ord_mulByThreeCoordHom_XClass_pos`, `ord_mulByThreeCoordHom_YClass_pos` — both generators of the
  closed point of the tripling coordinates vanish at `P`;
* **`comapProjPointThree_pointClosedPoint`** — the crux, at any affine point that is not
  `3`-torsion.  No `[W.IsElliptic]`;
* `eval_Φ_three_ne_zero_of_eval_Ψ₃_eq_zero`, `Y_ne_negY_of_eval_Ψ₃_eq_zero`,
  `ord_mulByThreeEndo_genX_neg`, **`comapProjPointThree_pointClosedPoint_of_eval_Ψ₃_eq_zero`** —
  the `3`-torsion places contract to the point at infinity;
* **`WeierstrassCurve.Affine.CoordinateRing.comapProjPointThree_projPointOfPoint`** — the headline,
  for every `P : W.Point`;
* `card_fibre_comapProjPointThree_projPointOfPoint`, `fibre_comapProjPointThree_eq_range` — the
  fibre over a rational point is the coset `{ P ⊕ R : R ∈ E[3] }`, with exactly nine elements;
* `ramificationIdxThree_eq_one_of_comapProjPointThree_eq_projPointOfPoint` — hence every
  ramification index over a rational point is `1`;
* **`pullbackDivisorThree_single_projPointOfPoint`** and
  **`pullbackDivisorThree_single_eq_sum_torsion`** —
  `[3]∗(S) = ∑_{p ↦ S} (p) = ∑_{R ∈ E[3]} (P ⊕ R)`.

## What is *not* here

* **`hprin` at `n = 3`, and therefore `#418`.**  The fibre description is an *input* to the
  class-group computation `∑_R toClass (P ⊕ R) − ∑_R toClass R = 9 · toClass P = toClass (3S) = 0`,
  not the computation itself.  That computation is
  `EllipticCurves.FunctionField.PullbackPrincipalityThree`, which consumes this file; nothing below
  performs it.
* **The fibre over a place that is not the closed point of an `F`-rational point.**  Over an
  algebraically closed base field every closed point *ought* to be rational, but that is a
  Nullstellensatz statement about `HeightOneSpectrum W.CoordinateRing` and it is nowhere in this
  tree.  So "`[3]` is unramified" is proved over the rational locus and only there; do not read the
  results below as an unramifiedness statement about `[3]` tout court.  `MulByTwoFibreAffine`
  carries the identical warning.
* **`#E[3] = 9` from any of this.**  `card_torsion_three` is an *input* to the counting, exactly as
  `card_torsion_two` is at `n = 2`.  ⚠️ And `∑_{p ↦ q} e_p = 9` is a statement about **places** of
  `F(W)`; the passage to a count of points runs through "a separable isogeny has `#ker = deg`",
  which no file in this tree contains.
* **The weighted identity** `∑ e_p · deg p = 9`.  `residueDegreeThree` does not exist, so
  `sum_ramificationIdxTwo_mul_residueDegreeTwo` still has no `n = 3` mirror.
* **General `n`.**  `mulByNEndo` does not exist; `[2]∗` and `[3]∗` are the two concrete
  endomorphisms this tree has.  `#404`'s general `ωₙ` is untouched.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2.3, III.4.10, III.8.1.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine.CoordinateRing

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}
  [IsDedekindDomain W.CoordinateRing] {x y : F}

/-! ### `[3]∗` on the two generators of a closed point -/

omit [DecidableEq F] [IsDedekindDomain W.CoordinateRing] in
/-- `[3]∗(X - x₃) = x ∘ [3] - x₃`. -/
theorem mulByThreeCoordHom_XClass (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (x₃ : F) :
    mulByThreeCoordHom h2 h3 (XClass W x₃)
      = mulByThreeEndo h2 h3 (genX W) - algebraMap F W.FunctionField x₃ := by
  rw [← mulByThreeEndo_algebraMap h2 h3, ← genPsi, XClass, C_sub, map_sub, map_sub,
    genPsi_mk_CC, ← genX, map_sub, mulByThreeEndo_algebraMap_base]

omit [DecidableEq F] [IsDedekindDomain W.CoordinateRing] in
/-- `[3]∗(Y - y₃) = y ∘ [3] - y₃`. -/
theorem mulByThreeCoordHom_YClass (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (y₃ : F) :
    mulByThreeCoordHom h2 h3 (YClass W (C y₃))
      = mulByThreeEndo h2 h3 (genY W) - algebraMap F W.FunctionField y₃ := by
  rw [← mulByThreeEndo_algebraMap h2 h3, ← genPsi, YClass, map_sub, map_sub, genPsi_mk_CC,
    show mk W Y = AdjoinRoot.root W.polynomial from rfl, ← genY, map_sub,
    mulByThreeEndo_algebraMap_base]

/-! ### The two generators of the tripled point vanish at `P`

⚠️ Both statements are about the **division form** `Φ₃(x)/ΨSq₃(x)` and `ω₃(x, y)/(2 ψ₃(x, y)³)`, not
about `addX`/`addY` of a tripling, and that is what makes them cheap: matched against
`mulByThreeEndo_genX`/`_genY` the numerator vanishes by `field_simp` and no tripling formula is
needed.  The identification of these coordinates with `3 • P` is `TriplingCoords`'s job and happens
one layer up, in `comapProjPointThree_projPointOfPoint_of_Y_ne`. -/

omit [DecidableEq F] in
/-- **`x ∘ [3] - Φ₃(x)/ΨSq₃(x)` vanishes at `P`**, for any affine `P` that is not `3`-torsion. -/
theorem ord_mulByThreeCoordHom_XClass_pos (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h : W.Equation x y) (hT : W.Ψ₃.eval x ≠ 0) :
    0 < ord (pointClosedPoint h)
      (mulByThreeCoordHom h2 h3 (XClass W ((W.Φ 3).eval x / (W.ΨSq 3).eval x))) := by
  have h3' : ((3 : ℤ) : F) ≠ 0 := by exact_mod_cast h3
  have hΨ0 : (W.ΨSq 3).eval x ≠ 0 := by
    rw [ΨSq_three_eval]; exact pow_ne_zero 2 hT
  refine ord_pos_of_eq_evalEval_div h ?_
    (n := C (W.Φ 3 - C ((W.Φ 3).eval x / (W.ΨSq 3).eval x) * W.ΨSq 3)) (d := C (W.ΨSq 3)) ?_ ?_ ?_
  · exact fun hz => XClass_ne_zero (W' := W) _
      (mulByThreeCoordHom_injective h2 h3 (by rw [hz, map_zero]))
  · rw [mulByThreeCoordHom_XClass, mulByThreeEndo_genX, map_Φ, map_ΨSq]
    have hB : ((W.ΨSq 3).map (algebraMap F W.FunctionField)).eval (genX W) ≠ 0 :=
      eval_map_genX_ne_zero (W.ΨSq_ne_zero h3')
    simp only [Polynomial.map_C, coe_mapRingHom, evalEval_C, Polynomial.map_sub,
      Polynomial.map_mul, eval_sub, eval_mul, eval_C]
    field_simp
  · simp only [evalEval_C, eval_sub, eval_mul, eval_C]
    rw [sub_eq_zero, div_mul_cancel₀ _ hΨ0]
  · simpa only [evalEval_C] using hΨ0

omit [DecidableEq F] in
/-- **`y ∘ [3] - ω₃(x, y)/(2 ψ₃(x, y)³)` vanishes at `P`**, for any affine `P` that is not
`3`-torsion.

The numerator carried through `ord_pos_of_eq_evalEval_div` is the bivariate polynomial whose
`evalEval` is `ω₃`, minus the value times the denominator; the `field_simp` that matches it against
`mulByThreeEndo_genY` is the only heavy step in this file and needs no raised limits. -/
theorem ord_mulByThreeCoordHom_YClass_pos (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h : W.Equation x y) (hT : W.Ψ₃.eval x ≠ 0) :
    0 < ord (pointClosedPoint h)
      (mulByThreeCoordHom h2 h3 (YClass W (C
        (((2 * y + W.a₁ * x + W.a₃) * ((W.preΨ 5).eval x - W.preΨ₄.eval x ^ 2) -
            W.a₁ * (W.Φ 3).eval x * (W.ψ 3).evalEval x y -
            W.a₃ * (W.ψ 3).evalEval x y ^ 3) / (2 * (W.ψ 3).evalEval x y ^ 3))))) := by
  have hs0 : (W.ψ 3).evalEval x y ≠ 0 := psiThree_evalEval_ne_zero h hT
  have hd0 : (2 : F) * (W.ψ 3).evalEval x y ^ 3 ≠ 0 :=
    mul_ne_zero h2 (pow_ne_zero 3 hs0)
  refine ord_pos_of_eq_evalEval_div h ?_
    (n := (2 * Y + C (C W.a₁ * Polynomial.X + C W.a₃)) * C (W.preΨ 5 - W.preΨ₄ ^ 2)
      - C (C W.a₁ * W.Φ 3) * W.ψ 3 - C (C W.a₃) * W.ψ 3 ^ 3
      - C (C (((2 * y + W.a₁ * x + W.a₃) * ((W.preΨ 5).eval x - W.preΨ₄.eval x ^ 2) -
            W.a₁ * (W.Φ 3).eval x * (W.ψ 3).evalEval x y -
            W.a₃ * (W.ψ 3).evalEval x y ^ 3) / (2 * (W.ψ 3).evalEval x y ^ 3)))
        * (2 * W.ψ 3 ^ 3))
    (d := 2 * W.ψ 3 ^ 3) ?_ ?_ ?_
  · exact fun hz => YClass_ne_zero (W' := W) _
      (mulByThreeCoordHom_injective h2 h3 (by rw [hz, map_zero]))
  · have hψg : ((W.ψ 3).map (mapRingHom (algebraMap F W.FunctionField))).evalEval
        (genX W) (genY W) ≠ 0 := by rw [← map_ψ]; exact psiThree_gen_ne h3
    have h2' : (2 : W.FunctionField) ≠ 0 := fun hz =>
      h2 ((algebraMap F W.FunctionField).injective (by rw [map_ofNat, map_zero]; exact hz))
    rw [mulByThreeCoordHom_YClass, mulByThreeEndo_genY]
    simp only [map_ψ, map_preΨ, map_preΨ₄, map_Φ, map_a₁, map_a₃, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X, Polynomial.map_ofNat, coe_mapRingHom, evalEval, eval_sub, eval_mul,
      eval_add, eval_pow, eval_C, eval_X, eval_ofNat] at hψg ⊢
    field_simp
    ring
  · simp only [evalEval, eval_sub, eval_mul, eval_add, eval_pow, eval_C, eval_X, eval_ofNat]
    rw [sub_eq_zero, div_mul_cancel₀ _ hd0]
    ring
  · simp only [evalEval, eval_mul, eval_pow, eval_ofNat]
    exact hd0

/-! ### The contraction at an affine point that is not `3`-torsion -/

omit [DecidableEq F] in
/-- `x ∘ [3]` is regular at an affine point that is not `3`-torsion: its denominator `ΨSq₃(x)` does
not vanish there.  The counterpart of `ord_mulByThreeEndo_genX_neg` below, on the other side of the
`3`-torsion locus. -/
theorem ord_mulByThreeEndo_genX_nonneg (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h : W.Equation x y) (hT : W.Ψ₃.eval x ≠ 0) :
    0 ≤ ord (pointClosedPoint h) (mulByThreeEndo h2 h3 (genX W)) := by
  have h3' : ((3 : ℤ) : F) ≠ 0 := by exact_mod_cast h3
  have hΨ0 : (W.ΨSq 3).eval x ≠ 0 := by
    rw [ΨSq_three_eval]; exact pow_ne_zero 2 hT
  have hΨ : ord (pointClosedPoint h)
      (((W.ΨSq 3).map (algebraMap F W.FunctionField)).eval (genX W)) = 0 := by
    have hnn := ord_eval_map_genX_nonneg (W := W) (pointClosedPoint h) (W.ΨSq 3)
    have hnp : ¬ 0 < ord (pointClosedPoint h)
        (((W.ΨSq 3).map (algebraMap F W.FunctionField)).eval (genX W)) := by
      rw [ord_eval_map_genX_pos_iff h (W.ΨSq_ne_zero h3')]
      exact hΨ0
    omega
  have hΦ := ord_eval_map_genX_nonneg (W := W) (pointClosedPoint h) (W.Φ 3)
  rw [mulByThreeEndo_genX, map_Φ, map_ΨSq, ord_div _ (eval_map_genX_ne_zero (W.Φ_ne_zero 3))
    (eval_map_genX_ne_zero (W.ΨSq_ne_zero h3')), hΨ]
  omega

omit [DecidableEq F] in
/-- **The crux: `[3]` on places is `[3]` on points at an affine non-`3`-torsion point.**

For `P = (x, y)` on `W` with `Ψ₃(x) ≠ 0`, the contraction of the closed point of `P` along `[3]∗`
is the closed point of the tripling coordinates `(Φ₃(x)/ΨSq₃(x), ω₃(x, y)/(2 ψ₃(x, y)³))`, whose
on-curve property is `EllipticCurves.Torsion.OmegaThree`'s `tripling_equation`.

⚠️ **`y ≠ negY x y` is deliberately absent.**  It is what `TriplingCoords` needs to identify those
coordinates with `3 • P`, and that identification happens one layer up; the place computation
itself does not care, because steps 1–2 are stated in division form.

The `3`-torsion case is `comapProjPointThree_pointClosedPoint_of_eval_Ψ₃_eq_zero` below and
`comapProjPointThree_none` (`#814`) is the case `P = O`; `comapProjPointThree_projPointOfPoint`
assembles all three.

No hypothesis on `F` beyond `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, and — unlike the `3`-torsion case,
which needs `Φ₃`/`ΨSq₃` coprimality and hence `IsUnit Δ` — **no `[W.IsElliptic]`**. -/
theorem comapProjPointThree_pointClosedPoint (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h : W.Equation x y) (hT : W.Ψ₃.eval x ≠ 0) :
    comapProjPointThree h2 h3 (some (pointClosedPoint h))
      = some (pointClosedPoint (tripling_equation h h2 (psiThree_evalEval_ne_zero h hT))) := by
  set h₃ := tripling_equation h h2 (psiThree_evalEval_ne_zero h hT) with hh3def
  have hX := ord_mulByThreeCoordHom_XClass_pos h2 h3 h hT
  have hY := ord_mulByThreeCoordHom_YClass_pos h2 h3 h hT
  cases hq : comapProjPointThree h2 h3 (some (pointClosedPoint h)) with
  | none =>
    exfalso
    have hkey := divisorProj_mulByThreeEndo_apply h2 h3 (f := genX W) genX_ne_zero
      (some (pointClosedPoint h))
    rw [divisorProj_apply_some, hq, divisorProj_apply_none, ordInfty_genX] at hkey
    have hpos := ramificationIdxThree_pos h2 h3 (some (pointClosedPoint h))
    have hnn := ord_mulByThreeEndo_genX_nonneg h2 h3 h hT
    rw [hkey] at hnn
    nlinarith [hpos, hnn]
  | some v =>
    have hmem : ∀ g : W.CoordinateRing, g ≠ 0 →
        0 < ord (pointClosedPoint h) (mulByThreeCoordHom h2 h3 g) → g ∈ v.asIdeal := by
      intro g hg hgpos
      have hkey := divisorProj_mulByThreeEndo_apply h2 h3 (f := genPsi W g)
        (fun hz => hg ((injective_iff_map_eq_zero _).mp
          (IsFractionRing.injective W.CoordinateRing W.FunctionField) _ hz))
        (some (pointClosedPoint h))
      rw [divisorProj_apply_some, hq, divisorProj_apply_some, genPsi,
        mulByThreeEndo_algebraMap] at hkey
      have hpos := ramificationIdxThree_pos h2 h3 (some (pointClosedPoint h))
      rw [hkey] at hgpos
      refine (ord_algebraMap_pos_iff v hg).1 ?_
      nlinarith [hpos, hgpos]
    have hle : (pointClosedPoint h₃).asIdeal ≤ v.asIdeal := by
      rw [pointClosedPoint_asIdeal, XYIdeal, Ideal.span_le]
      rintro g (rfl | rfl)
      · exact hmem _ (XClass_ne_zero _) hX
      · exact hmem _ (YClass_ne_zero _) hY
    have hmax : (pointClosedPoint h₃).asIdeal.IsMaximal :=
      Ideal.IsPrime.isMaximal (pointClosedPoint h₃).isPrime (pointClosedPoint h₃).ne_bot
    exact congrArg some (HeightOneSpectrum.ext (hmax.eq_of_le v.isPrime.ne_top hle).symm)

/-! ### The tripling coordinates at a `2`-torsion point

The family `TriplingCoords` cannot reach, and which has no `n = 2` analogue.  Both computations are
`Ψ₂Sq(x) = 0` substituted into the division-polynomial formulas. -/

omit [DecidableEq F] [IsDedekindDomain W.CoordinateRing] in
/-- `ψ₃(x, y) = Ψ₃(x)` at a point of `W`. -/
theorem psiThree_evalEval_eq (h : W.Equation x y) :
    (W.ψ 3).evalEval x y = W.Ψ₃.eval x := by
  rw [ψ_evalEval h 3, Ψ_three, evalEval_C]

omit [DecidableEq F] [IsDedekindDomain W.CoordinateRing] in
/-- **`x(3P) = x(P)` at a `2`-torsion point.**  `Φ₃ = X·Ψ₃² − preΨ₄·Ψ₂Sq` and `Ψ₂Sq(x) = 0`, so the
quotient `Φ₃(x)/ΨSq₃(x)` collapses to `x` — as it must, since `3 • P = P` there. -/
theorem tripling_eq_self_of_Y_eq (h : W.Equation x y) (hy : y = W.negY x y)
    (hT : W.Ψ₃.eval x ≠ 0) :
    (W.Φ 3).eval x / (W.ΨSq 3).eval x = x := by
  have hs : 2 * y + W.a₁ * x + W.a₃ = 0 := by rw [negY] at hy; linear_combination hy
  have hp : W.Ψ₂Sq.eval x = 0 := by rw [Ψ₂Sq_eval_eq_sq h, hs]; ring
  rw [Φ_three_eval, hp, ΨSq_three_eval]
  field_simp
  ring

omit [DecidableEq F] [IsDedekindDomain W.CoordinateRing] in
/-- **`y(3P) = y(P)` at a `2`-torsion point.**  With `2y + a₁x + a₃ = 0` the first term of `ω₃`
vanishes and the remaining `−a₁Φ₃ψ₃ − a₃ψ₃³` is `2y·ψ₃³`, using `Φ₃(x) = x·Ψ₃(x)²` from the
computation above. -/
theorem omegaThree_div_eq_self_of_Y_eq (h2 : (2 : F) ≠ 0) (h : W.Equation x y)
    (hy : y = W.negY x y) (hT : W.Ψ₃.eval x ≠ 0) :
    ((2 * y + W.a₁ * x + W.a₃) * ((W.preΨ 5).eval x - W.preΨ₄.eval x ^ 2) -
        W.a₁ * (W.Φ 3).eval x * (W.ψ 3).evalEval x y -
        W.a₃ * (W.ψ 3).evalEval x y ^ 3) / (2 * (W.ψ 3).evalEval x y ^ 3) = y := by
  have hs : 2 * y + W.a₁ * x + W.a₃ = 0 := by rw [negY] at hy; linear_combination hy
  have hp : W.Ψ₂Sq.eval x = 0 := by rw [Ψ₂Sq_eval_eq_sq h, hs]; ring
  have hψ : (W.ψ 3).evalEval x y = W.Ψ₃.eval x := psiThree_evalEval_eq h
  have hΦ : (W.Φ 3).eval x = x * W.Ψ₃.eval x ^ 2 := by
    rw [Φ_three_eval, hp]; ring
  rw [hs, hψ, hΦ, div_eq_iff (mul_ne_zero h2 (pow_ne_zero 3 hT))]
  linear_combination (-(W.Ψ₃.eval x ^ 3)) * hs

/-! ### The `3`-torsion places contract to the point at infinity

The mirror of `MulByTwoFibreInfinity`'s step 1, and the same argument: `x ∘ [3] = Φ₃(x)/ΨSq₃(x)` has
a *pole* at a root of `Ψ₃`, so the contracted place cannot be affine. -/

variable [W.IsElliptic]

omit [DecidableEq F] [IsDedekindDomain W.CoordinateRing] in
/-- **`Φ₃` does not vanish at a root of `Ψ₃`.**  `Φ₃` and `ΨSq₃ = Ψ₃²` are coprime on an elliptic
curve (`isCoprime_Φ_three_ΨSq_three`, the `n = 3` analogue of `#681`'s Bézout identity, proved by a
congruence argument because the `n = 2` certificate is a `17 × 17` Sylvester determinant here). -/
theorem eval_Φ_three_ne_zero_of_eval_Ψ₃_eq_zero (hT : W.Ψ₃.eval x = 0) :
    (W.Φ 3).eval x ≠ 0 := by
  obtain ⟨a, b, hab⟩ := W.isCoprime_Φ_three_ΨSq_three
  intro hz
  have hb := congrArg (Polynomial.eval x) hab
  have hΨ : (W.ΨSq 3).eval x = 0 := by rw [ΨSq_three_eval, hT]; ring
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, hz, hΨ,
    mul_zero, add_zero] at hb
  exact one_ne_zero hb.symm

omit [DecidableEq F] [IsDedekindDomain W.CoordinateRing] in
/-- **A `3`-torsion point is not `2`-torsion.**  `y = negY x y` forces `Ψ₂Sq(x) = 0`, and `Ψ₃` and
`Ψ₂Sq` are coprime on an elliptic curve (`isCoprime_Ψ₃_Ψ₂Sq`).

This is what closes the gap between the two excluded families of `TriplingCoords`: the uniform
statement below never has to handle a point that is both. -/
theorem Y_ne_negY_of_eval_Ψ₃_eq_zero (h : W.Equation x y) (hT : W.Ψ₃.eval x = 0) :
    y ≠ W.negY x y := by
  intro hy
  have hs : 2 * y + W.a₁ * x + W.a₃ = 0 := by rw [negY] at hy; linear_combination hy
  have hp : W.Ψ₂Sq.eval x = 0 := by rw [Ψ₂Sq_eval_eq_sq h, hs]; ring
  obtain ⟨a, b, hab⟩ := W.isCoprime_Ψ₃_Ψ₂Sq
  have hb := congrArg (Polynomial.eval x) hab
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, hT, hp,
    mul_zero, add_zero] at hb
  exact one_ne_zero hb.symm

omit [DecidableEq F] in
/-- **`x ∘ [3]` has a pole at every affine `3`-torsion point.** -/
theorem ord_mulByThreeEndo_genX_neg (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (h : W.Equation x y)
    (hT : W.Ψ₃.eval x = 0) :
    ord (pointClosedPoint h) (mulByThreeEndo h2 h3 (genX W)) < 0 := by
  have h3' : ((3 : ℤ) : F) ≠ 0 := by exact_mod_cast h3
  have hΨ : (W.ΨSq 3).eval x = 0 := by rw [ΨSq_three_eval, hT]; ring
  have hΦ0 : ord (pointClosedPoint h)
      (((W.Φ 3).map (algebraMap F W.FunctionField)).eval (genX W)) = 0 := by
    have hnn := ord_eval_map_genX_nonneg (W := W) (pointClosedPoint h) (W.Φ 3)
    have hnp : ¬ 0 < ord (pointClosedPoint h)
        (((W.Φ 3).map (algebraMap F W.FunctionField)).eval (genX W)) := by
      rw [ord_eval_map_genX_pos_iff h (W.Φ_ne_zero 3)]
      exact eval_Φ_three_ne_zero_of_eval_Ψ₃_eq_zero hT
    omega
  have hΨ0 : 0 < ord (pointClosedPoint h)
      (((W.ΨSq 3).map (algebraMap F W.FunctionField)).eval (genX W)) :=
    (ord_eval_map_genX_pos_iff h (W.ΨSq_ne_zero h3')).2 hΨ
  rw [mulByThreeEndo_genX h2 h3, map_Φ, map_ΨSq,
    ord_div _ (eval_map_genX_ne_zero (W.Φ_ne_zero 3))
      (eval_map_genX_ne_zero (W.ΨSq_ne_zero h3')), hΦ0]
  omega

omit [DecidableEq F] in
/-- **`[3]` contracts every affine `3`-torsion place to the place at infinity.**

The affine half of the geometric statement that `[3]` maps `E[3]` to `O`, read on places, and the
`n = 3` mirror of `comapProjPointTwo_pointClosedPoint_of_eval_Ψ₂Sq_eq_zero` (`#774`). -/
theorem comapProjPointThree_pointClosedPoint_of_eval_Ψ₃_eq_zero (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (h : W.Equation x y) (hT : W.Ψ₃.eval x = 0) :
    comapProjPointThree h2 h3 (some (pointClosedPoint h)) = none := by
  have hkey := divisorProj_mulByThreeEndo_apply h2 h3 (f := genX W) genX_ne_zero
    (some (pointClosedPoint h))
  rw [divisorProj_apply_some] at hkey
  cases hq : comapProjPointThree h2 h3 (some (pointClosedPoint h)) with
  | none => rfl
  | some v =>
    exfalso
    rw [hq, divisorProj_apply_some] at hkey
    have hlt := ord_mulByThreeEndo_genX_neg h2 h3 h hT
    have hge : (0 : ℤ) ≤ ord v (genX W) := by
      rw [genX, genPsi]
      exact ord_algebraMap_nonneg v _
    have hnn : (0 : ℤ) ≤ ramificationIdxThree h2 h3 (some (pointClosedPoint h)) * ord v (genX W) :=
      mul_nonneg (ramificationIdxThree_pos h2 h3 _).le hge
    omega

/-! ### The uniform statement on the rational locus -/

/-- The crux in `Point` language, at an affine point that is neither `2`- nor `3`-torsion.  This is
the one place `EllipticCurves.Torsion.TriplingCoords` is used. -/
theorem comapProjPointThree_projPointOfPoint_of_Y_ne (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {h : W.Nonsingular x y} (hy : y ≠ W.negY x y) (hT : W.Ψ₃.eval x ≠ 0) :
    comapProjPointThree h2 h3 (projPointOfPoint W (Point.some x y h))
      = projPointOfPoint W ((3 : ℕ) • Point.some x y h) := by
  rw [nsmul_three_eq_some h2 hy hT, projPointOfPoint_some, projPointOfPoint_some]
  exact comapProjPointThree_pointClosedPoint h2 h3 h.left hT

omit [W.IsElliptic] in
/-- The same at an affine `2`-torsion point that is not `3`-torsion, where `3 • P = P` and the
tripling coordinates collapse to `(x, y)`. -/
theorem comapProjPointThree_projPointOfPoint_of_Y_eq (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {h : W.Nonsingular x y} (hy : y = W.negY x y) (hT : W.Ψ₃.eval x ≠ 0) :
    comapProjPointThree h2 h3 (projPointOfPoint W (Point.some x y h))
      = projPointOfPoint W ((3 : ℕ) • Point.some x y h) := by
  have hthree : (3 : ℕ) • Point.some x y h = Point.some x y h := by
    rw [three'_nsmul, Point.add_self_of_Y_eq hy, zero_add]
  rw [hthree, projPointOfPoint_some, comapProjPointThree_pointClosedPoint h2 h3 h.left hT]
  refine congrArg some (HeightOneSpectrum.ext ?_)
  rw [pointClosedPoint_asIdeal, pointClosedPoint_asIdeal,
    tripling_eq_self_of_Y_eq h.left hy hT, omegaThree_div_eq_self_of_Y_eq h2 h.left hy hT]

/-- The two cases above, at any affine point that is not `3`-torsion. -/
theorem comapProjPointThree_projPointOfPoint_of_Ψ₃_ne (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {h : W.Nonsingular x y} (hT : W.Ψ₃.eval x ≠ 0) :
    comapProjPointThree h2 h3 (projPointOfPoint W (Point.some x y h))
      = projPointOfPoint W ((3 : ℕ) • Point.some x y h) := by
  by_cases hy : y = W.negY x y
  · exact comapProjPointThree_projPointOfPoint_of_Y_eq h2 h3 hy hT
  · exact comapProjPointThree_projPointOfPoint_of_Y_ne h2 h3 hy hT

/-- **The place contraction of `[3]∗` is the tripling map, on the whole rational locus.**

```
comapProjPointThree h2 h3 (projPointOfPoint P) = projPointOfPoint (3 • P)
```

with no case hypothesis.  The four cases are `comapProjPointThree_none` (`#814`, `P = O`),
`comapProjPointThree_pointClosedPoint_of_eval_Ψ₃_eq_zero` (`P` affine `3`-torsion), and the two
halves of `comapProjPointThree_projPointOfPoint_of_Ψ₃_ne` (`P` affine, not `3`-torsion, split on
whether it is `2`-torsion).

⚠️ The `3`-torsion branch uses `Y_ne_negY_of_eval_Ψ₃_eq_zero` to know that
`mem_torsion_three_some_iff` applies — a `3`-torsion point is not `2`-torsion — and that is the only
place the coprimality of `Ψ₃` and `Ψ₂Sq` is needed for the assembly rather than for the pole.

This is the `n = 3` mirror of `#774`'s deliverable 1, and the last geometric rung below `hprin` at
`n = 3`. -/
theorem comapProjPointThree_projPointOfPoint (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (P : W.Point) :
    comapProjPointThree h2 h3 (projPointOfPoint W P)
      = projPointOfPoint W ((3 : ℕ) • P) := by
  rcases P with _ | ⟨x, y, hns⟩
  · rw [← Point.zero_def, smul_zero, projPointOfPoint_zero]
    exact comapProjPointThree_none h2 h3
  · by_cases hT : W.Ψ₃.eval x = 0
    · have hy := Y_ne_negY_of_eval_Ψ₃_eq_zero hns.left hT
      have hzero : (3 : ℕ) • Point.some x y hns = 0 :=
        mem_torsion_iff.mp ((mem_torsion_three_some_iff hy).2 hT)
      rw [hzero, projPointOfPoint_zero, projPointOfPoint_some]
      exact comapProjPointThree_pointClosedPoint_of_eval_Ψ₃_eq_zero h2 h3 hns.left hT
    · exact comapProjPointThree_projPointOfPoint_of_Ψ₃_ne h2 h3 hT

/-! ### The fibre over a rational point, and the divisor identity -/

/-- **`P ⊕ R` lies over `3 • P`, for every `R ∈ E[3]`.**  The nine preimages of a rational point,
exhibited as a coset of `E[3]`. -/
theorem comapProjPointThree_add_torsion_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {S P : W.Point} (hP : (3 : ℕ) • P = S) (R : W.torsion 3) :
    comapProjPointThree h2 h3 (projPointOfPoint W (P + R)) = projPointOfPoint W S := by
  rw [comapProjPointThree_projPointOfPoint h2 h3, smul_add, hP, mem_torsion_iff.mp R.2, add_zero]

omit [W.IsElliptic] in
/-- **`R ↦ P ⊕ R` is injective into the places**, for `R` ranging over `E[3]`. -/
theorem projPointOfPoint_add_injective_three (P : W.Point) :
    Function.Injective fun R : W.torsion 3 => projPointOfPoint W (P + R) :=
  fun _ _ hEq => Subtype.ext (add_right_injective P (projPointOfPoint_injective hEq))

section IsAlgClosed

variable [IsAlgClosed F]

omit [DecidableEq F] in
/-- **The fibre of `[3]` over any rational point has exactly nine elements.**

`≥ 9` is `{ P ⊕ R : R ∈ E[3] }` for a `P` with `3 • P = S` (`exists_nsmul_three_eq`), nine distinct
elements by `card_torsion_three` and `projPointOfPoint_add_injective_three`, all in the fibre by
`comapProjPointThree_add_torsion_three`; `≤ 9` is `#815`'s
`card_fibre_comapProjPointThree_le_nine`. -/
theorem card_fibre_comapProjPointThree_projPointOfPoint (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (S : W.Point) :
    (finite_comapProjPointThree_preimage_singleton h2 h3
      (projPointOfPoint W S)).toFinset.card = 9 := by
  classical
  haveI := W.finite_torsion_three (F := F) h3
  haveI := Fintype.ofFinite (W.torsion 3)
  obtain ⟨P, hP⟩ := exists_nsmul_three_eq h2 S
  refine le_antisymm (card_fibre_comapProjPointThree_le_nine h2 h3 _) ?_
  have hcard : Fintype.card (W.torsion 3) = 9 := by
    rw [← Nat.card_eq_fintype_card, card_torsion_three h2 h3]
  rw [← hcard, ← Finset.card_univ]
  exact Finset.card_le_card_of_injOn (fun R => projPointOfPoint W (P + R))
    (fun R _ => (Set.Finite.mem_toFinset _).2 (comapProjPointThree_add_torsion_three h2 h3 hP R))
    (Set.injOn_of_injective (projPointOfPoint_add_injective_three P))

/-- **The fibre of `[3]` over a rational point *is* the coset `{ P ⊕ R : R ∈ E[3] }`**, for any `P`
with `3 • P = S`.

The inclusion `⊇` is `comapProjPointThree_add_torsion_three`; the reverse is pure counting — nine
distinct elements inside a nine-element set, with no further geometry.

Stated with `Set.range` rather than a `Finset.image` because `ProjPoint W` carries no `DecidableEq`,
and baking a classical one into the statement would restrict who can apply it. -/
theorem fibre_comapProjPointThree_eq_range (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {S P : W.Point} (hP : (3 : ℕ) • P = S) :
    comapProjPointThree h2 h3 ⁻¹' {projPointOfPoint W S}
      = Set.range fun R : W.torsion 3 => projPointOfPoint W (P + R) := by
  classical
  haveI := W.finite_torsion_three h3
  haveI := Fintype.ofFinite (W.torsion 3)
  have hfin := finite_comapProjPointThree_preimage_singleton h2 h3 (projPointOfPoint W S)
  have hsub : (Set.range fun R : W.torsion 3 => projPointOfPoint W (P + R))
      ⊆ comapProjPointThree h2 h3 ⁻¹' {projPointOfPoint W S} := by
    rintro p ⟨R, rfl⟩
    exact comapProjPointThree_add_torsion_three h2 h3 hP R
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ hfin).symm
  have hc1 : (comapProjPointThree h2 h3 ⁻¹' {projPointOfPoint W S}).ncard = 9 := by
    rw [Set.ncard_eq_toFinset_card _ hfin]
    exact card_fibre_comapProjPointThree_projPointOfPoint h2 h3 S
  have hc2 : (Set.range fun R : W.torsion 3 => projPointOfPoint W (P + R)).ncard = 9 := by
    rw [← Nat.card_coe_set_eq,
      Nat.card_range_of_injective (projPointOfPoint_add_injective_three P),
      card_torsion_three h2 h3]
  omega

omit [DecidableEq F] in
/-- **`[3]` is unramified over every rational point.**  Nine positive indices summing to `9`
(`#815`'s `sum_ramificationIdxThree_eq_nine` against the count above) are all `1`.

⚠️ This is *not* "`[3]` is unramified": a place lying over a closed point that is **not** the closed
point of an `F`-rational point is untouched, and this tree has no proof that there are none.  See
the module docstring. -/
theorem ramificationIdxThree_eq_one_of_comapProjPointThree_eq_projPointOfPoint (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {p : ProjPoint W} {S : W.Point}
    (hp : comapProjPointThree h2 h3 p = projPointOfPoint W S) :
    ramificationIdxThree h2 h3 p = 1 := by
  classical
  set s := (finite_comapProjPointThree_preimage_singleton h2 h3
    (projPointOfPoint W S)).toFinset with hs
  have hmem : p ∈ s := (Set.Finite.mem_toFinset _).2 hp
  have hcard : s.card = 9 := card_fibre_comapProjPointThree_projPointOfPoint h2 h3 S
  have hsum : ∑ q ∈ s, (ramificationIdxThree h2 h3 q).toNat = 9 :=
    sum_ramificationIdxThree_eq_nine h2 h3 _
  have hsplit : (ramificationIdxThree h2 h3 p).toNat
      + ∑ q ∈ s.erase p, (ramificationIdxThree h2 h3 q).toNat = 9 := by
    rw [Finset.add_sum_erase _ (fun q => (ramificationIdxThree h2 h3 q).toNat) hmem]
    exact hsum
  have hlow : (s.erase p).card ≤ ∑ q ∈ s.erase p, (ramificationIdxThree h2 h3 q).toNat := by
    simpa using Finset.card_nsmul_le_sum (s.erase p)
      (fun q => (ramificationIdxThree h2 h3 q).toNat) 1
      (fun q _ => by have := ramificationIdxThree_pos h2 h3 q; omega)
  have hec : (s.erase p).card = 8 := by rw [Finset.card_erase_of_mem hmem, hcard]
  have hpos := ramificationIdxThree_pos h2 h3 p
  omega

omit [DecidableEq F] in
/-- **The fibre description of `[3]∗` over a rational point**: `[3]∗(S) = ∑_{p ↦ S} (p)`, every
coefficient `1`.

At `S = O` this computes `[3]∗(O)`; together with the affine case,

```
[3]∗((S) − (O)) = ∑_{p ↦ S} (p) − ∑_{p ↦ O} (p).
```

`pullbackDivisorThree_single_eq_sum_torsion` rewrites each fibre as a sum over `E[3]`. -/
theorem pullbackDivisorThree_single_projPointOfPoint (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (S : W.Point) :
    pullbackDivisorThree h2 h3 (Finsupp.single (projPointOfPoint W S) (1 : ℤ))
      = ∑ p ∈ (finite_comapProjPointThree_preimage_singleton h2 h3
          (projPointOfPoint W S)).toFinset, Finsupp.single p (1 : ℤ) := by
  classical
  ext q
  have hrhs : (∑ p ∈ (finite_comapProjPointThree_preimage_singleton h2 h3
        (projPointOfPoint W S)).toFinset, Finsupp.single p (1 : ℤ)) q
      = if comapProjPointThree h2 h3 q = projPointOfPoint W S then 1 else 0 := by
    rw [Finset.sum_apply', Finset.sum_congr rfl fun p _ => Finsupp.single_apply,
      Finset.sum_ite_eq' _ q fun _ => (1 : ℤ)]
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]
  rw [pullbackDivisorThree_apply, hrhs]
  by_cases hq : comapProjPointThree h2 h3 q = projPointOfPoint W S
  · rw [hq, Finsupp.single_eq_same, mul_one,
      ramificationIdxThree_eq_one_of_comapProjPointThree_eq_projPointOfPoint h2 h3 hq, if_pos rfl]
  · rw [Finsupp.single_apply, if_neg fun hc => hq hc.symm, mul_zero, if_neg hq]

/-- **The `n = 3` form of `#774`'s formula, in the shape `#418` consumes it**: for any `P` with
`3 • P = S`,

```
[3]∗(S) = ∑_{R ∈ E[3]} (P ⊕ R).
```

Subtracting the same statement at `S = O` (where `P` may be taken to be `O`, so that the sum is
`∑_R (R)`) gives `[3]∗((S) − (O)) = ∑_{R ∈ E[3]} ((P ⊕ R) − (R))`.

The `[Fintype (W.torsion 3)]` is carried in the statement rather than produced inside it: the sum
cannot be written without it, and pushing `Fintype.ofFinite` into a statement is a noncomputable
leak.  `finite_torsion_three` supplies it at the point of use. -/
theorem pullbackDivisorThree_single_eq_sum_torsion [Fintype (W.torsion 3)] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {S P : W.Point} (hP : (3 : ℕ) • P = S) :
    pullbackDivisorThree h2 h3 (Finsupp.single (projPointOfPoint W S) (1 : ℤ))
      = ∑ R : W.torsion 3, Finsupp.single (projPointOfPoint W (P + R)) (1 : ℤ) := by
  classical
  ext q
  rw [pullbackDivisorThree_apply, Finset.sum_apply',
    Finset.sum_congr rfl fun R _ => Finsupp.single_apply]
  by_cases hq : comapProjPointThree h2 h3 q = projPointOfPoint W S
  · obtain ⟨R₀, hR₀⟩ : q ∈ Set.range fun R : W.torsion 3 => projPointOfPoint W (P + R) := by
      rw [← fibre_comapProjPointThree_eq_range h2 h3 hP]; exact hq
    rw [hq, Finsupp.single_eq_same, mul_one,
      ramificationIdxThree_eq_one_of_comapProjPointThree_eq_projPointOfPoint h2 h3 hq,
      Finset.sum_eq_single R₀ (fun R _ hRne => if_neg fun hc =>
        hRne (projPointOfPoint_add_injective_three P (hc.trans hR₀.symm)))
      (fun hc => absurd (Finset.mem_univ R₀) hc), if_pos hR₀]
  · rw [Finsupp.single_apply, if_neg fun hc => hq hc.symm, mul_zero, Finset.sum_eq_zero]
    intro R _
    refine if_neg fun hc => hq ?_
    rw [← hc]
    exact comapProjPointThree_add_torsion_three h2 h3 hP R

end IsAlgClosed

/-! ### Non-vacuity

The headline statements carry `[IsDedekindDomain W.CoordinateRing]`, `[W.IsElliptic]` and (for the
counting) `[IsAlgClosed F]`, and `comapProjPointThree` is extracted by choice, so a curve on which
the whole chain elaborates with every instance discharged is committed rather than asserted.

`y² + y = x³` over `AlgebraicClosure ℚ` is the `n = 3` certificate curve of this tree, used by
`TranslationActionThree`, `MulByThreeGalois` and `MulByThreeRamification`; the `n = 2` curve
`y² = x³ − x` has no rational `3`-torsion point, and no `ℚ`-curve can witness a statement that
needs an algebraically closed base field. -/

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

open scoped Classical in
/-- **`[3]` on places is `[3]` on points, on a curve that exists.** -/
example (P : exampleCurveThree.Point) :
    comapProjPointThree exampleTwo exampleThree (projPointOfPoint exampleCurveThree P)
      = projPointOfPoint exampleCurveThree ((3 : ℕ) • P) :=
  comapProjPointThree_projPointOfPoint exampleTwo exampleThree P

open scoped Classical in
/-- **Every fibre over a rational point has nine elements, on the same curve.** -/
example (S : exampleCurveThree.Point) :
    (finite_comapProjPointThree_preimage_singleton exampleTwo exampleThree
      (projPointOfPoint exampleCurveThree S)).toFinset.card = 9 :=
  card_fibre_comapProjPointThree_projPointOfPoint exampleTwo exampleThree S

open scoped Classical in
/-- The fibre description, on the same curve. -/
example (S : exampleCurveThree.Point) :
    pullbackDivisorThree exampleTwo exampleThree
        (Finsupp.single (projPointOfPoint exampleCurveThree S) (1 : ℤ))
      = ∑ p ∈ (finite_comapProjPointThree_preimage_singleton exampleTwo exampleThree
          (projPointOfPoint exampleCurveThree S)).toFinset, Finsupp.single p (1 : ℤ) :=
  pullbackDivisorThree_single_projPointOfPoint exampleTwo exampleThree S

open scoped Classical in
/-- **The formula `#418` consumes**, on the same curve: `[3]∗(S) = ∑_{R ∈ E[3]} (P ⊕ R)`. -/
example [Fintype (exampleCurveThree.torsion 3)] (S P : exampleCurveThree.Point)
    (hP : (3 : ℕ) • P = S) :
    pullbackDivisorThree exampleTwo exampleThree
        (Finsupp.single (projPointOfPoint exampleCurveThree S) (1 : ℤ))
      = ∑ R : exampleCurveThree.torsion 3,
          Finsupp.single (projPointOfPoint exampleCurveThree (P + R)) (1 : ℤ) :=
  pullbackDivisorThree_single_eq_sum_torsion exampleTwo exampleThree hP

open scoped Classical in
/-- The `Fintype` the statement above carries is available, not an assumption in disguise. -/
example : Finite (exampleCurveThree.torsion 3) :=
  exampleCurveThree.finite_torsion_three exampleThree

end Nonvacuity

end WeierstrassCurve.Affine.CoordinateRing
