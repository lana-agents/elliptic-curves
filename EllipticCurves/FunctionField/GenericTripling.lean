/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.GenericDoubling
import EllipticCurves.FunctionField.MulByThreeEndomorphism

/-!
# The tripling correspondence: `mulByThreeEndo` acts as `[3]•` on the generic point

Let `W` be an elliptic curve over a field `F` of characteristic `≠ 2, 3`.  Building on
`GenericPoint.lean` (the generic point `𝒫 = (genX W, genY W)` as an element of the Mathlib group
`(W ⁄ F(W)).Point`) and the merged doubling correspondence `GenericDoubling.lean`
(`genericPoint_add_self : 𝒫 + 𝒫 = (mulByTwoEndo genX, mulByTwoEndo genY)`), this file identifies the
multiplication-by-`3` endomorphism `mulByThreeEndo : F(W) →+* F(W)` with the *group triple*
`𝒫 ↦ 𝒫 + 𝒫 + 𝒫 = [3]•𝒫`:

```
𝒫 + 𝒫 + 𝒫 = (mulByThreeEndo h2 h3 (genX W), mulByThreeEndo h2 h3 (genY W)).
```

`mulByThreeEndo` sends the coordinate generators to the classical division-polynomial tripling
coordinates `(Φ₃/ΨSq₃, ω₃/(2 ψ₃³))` (`mulByThreeEndo_genX`/`_genY`), so this is exactly the tripling
formula at the generic point — the `n = 3` mirror of `genericPoint_add_self`, and the `n = 3` slice
of the bridge `mulByNEndo = [n]•`.

## Contents

* `nonsingular_mulByThreeEndo_gen`  — the tripling coordinates
  `(mulByThreeEndo genX, mulByThreeEndo genY)` are a nonsingular point (they lie on the curve by
  `tripling_equation_gen`);
* `mulByTwoEndo_genX_ne_genX`       — `x(2•𝒫) ≠ x(𝒫)` at the generic point, so the secant sum
  `(2•𝒫) + 𝒫` takes the `add_of_X_ne` branch of the affine addition law;
* `addX_gen_eq_mulByThree`          — the `x`-coordinate identity `addX = mulByThreeEndo genX`;
* `addY_gen_eq_mulByThree`          — the `y`-coordinate identity `addY = mulByThreeEndo genY`;
* `genericPoint_add_add_self`       — the **tripling correspondence** `𝒫 + 𝒫 + 𝒫 = (mulByThreeEndo
  genX, mulByThreeEndo genY)`.

Everything here is Ward- and normality-independent: it needs only `[Field F] [W.IsElliptic]`,
`(2 : F) ≠ 0`, and `(3 : F) ≠ 0`, no `IsDedekindDomain` and no elliptic-net machinery.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], Exercise 3.7, III.8.
-/

open Polynomial

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-- **The tripling coordinates form a nonsingular point.** The images
`mulByThreeEndo h2 h3 (genX W)`, `mulByThreeEndo h2 h3 (genY W)` are the classical
division-polynomial tripling coordinates `(Φ₃/ΨSq₃, ω₃/(2 ψ₃³))` (`mulByThreeEndo_genX`/`_genY`),
which lie on the base-changed elliptic curve by `tripling_equation_gen`; on an elliptic curve,
every equation point is nonsingular. -/
theorem nonsingular_mulByThreeEndo_gen (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    (W.map (algebraMap F W.FunctionField)).Nonsingular
      (mulByThreeEndo h2 h3 (genX W)) (mulByThreeEndo h2 h3 (genY W)) := by
  rw [mulByThreeEndo_genX, mulByThreeEndo_genY]
  exact (W.map (algebraMap F W.FunctionField)).equation_iff_nonsingular.mp
    (tripling_equation_gen h2 h3)

omit [W.IsElliptic] in
/-- **`x(2•𝒫) ≠ x(𝒫)`.** The `x`-coordinate of the doubled generic point,
`mulByTwoEndo h2 (genX W) = Φ₂(genX)/Ψ₂Sq(genX)`, is different from the generic `x`-coordinate
`genX W`.  Geometrically `x(2P) = x(P) ⟺ 2P = ±P ⟺ 3P = O` (or `P = O`), false at the generic point.
Algebraically: were they equal, `genX` would be a root of the nonzero `F`-polynomial
`Φ₂ - X·Ψ₂Sq` (its degree-`4` coefficient is `1 - 4 = -3 ≠ 0`, using `(3 : F) ≠ 0`), contradicting
`transcendental_genX`.  This distinctness is what makes the secant sum `(2•𝒫) + 𝒫` take the
`add_of_X_ne` branch of the affine addition law. -/
theorem mulByTwoEndo_genX_ne_genX (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    mulByTwoEndo h2 (genX W) ≠ genX W := by
  rw [mulByTwoEndo_genX]
  -- The doubling denominator `Ψ₂Sq(genX)` does not vanish (the generic point is not `2`-torsion).
  have hden : ((W.map (algebraMap F W.FunctionField)).Ψ₂Sq).eval (genX W) ≠ 0 := by
    have hsq := ψ_sq_evalEval (W := W.map (algebraMap F W.FunctionField)) equation_gen 2
    rw [ΨSq_two] at hsq
    rw [← hsq]
    exact pow_ne_zero 2 (psiTwo_gen_ne h2)
  intro hcontra
  -- If `x(2P) = x(P)`, then `Φ₂(genX) = genX · Ψ₂Sq(genX)`.
  have hrel : ((W.map (algebraMap F W.FunctionField)).Φ 2).eval (genX W)
      = genX W * ((W.map (algebraMap F W.FunctionField)).Ψ₂Sq).eval (genX W) := by
    field_simp [hden] at hcontra
    linear_combination hcontra
  -- The candidate annihilating `F`-polynomial of `genX`.
  set q : F[X] := W.Φ 2 - X * W.Ψ₂Sq with hq
  -- `q` is nonzero: its degree-`4` coefficient is `1 - 4 = -3 ≠ 0`.
  have hqne : q ≠ 0 := by
    intro h0
    have hcoeff : q.coeff 4 = -3 := by
      rw [hq, coeff_sub, coeff_X_mul,
        show (4 : ℕ) = (2 : ℤ).natAbs ^ 2 by decide, W.coeff_Φ 2, W.coeff_Ψ₂Sq]
      norm_num
    rw [h0, coeff_zero] at hcoeff
    exact h3 (by linear_combination hcoeff)
  -- `genX` is a root of `q`, hence algebraic over `F` — contradicting `transcendental_genX`.
  refine transcendental_genX (W := W) ⟨q, hqne, ?_⟩
  have e1 : (aeval (genX W)) (W.Φ 2)
      = ((W.map (algebraMap F W.FunctionField)).Φ 2).eval (genX W) := by
    rw [map_Φ, aeval_def, eval₂_eq_eval_map]
  have e2 : (aeval (genX W)) W.Ψ₂Sq
      = ((W.map (algebraMap F W.FunctionField)).Ψ₂Sq).eval (genX W) := by
    rw [map_Ψ₂Sq, aeval_def, eval₂_eq_eval_map]
  rw [hq, map_sub, map_mul, aeval_X, e1, e2, hrel]
  ring


set_option maxHeartbeats 2000000 in
-- The tripling `x`-identity clears the doubling denominators into a large division-polynomial
-- relation whose `linear_combination`/`ring` normalisation needs a raised heartbeat limit.
open Classical in
omit [W.IsElliptic] in
/-- **The `x`-coordinate of the tripling formula.** The `x`-coordinate `addX` of the secant sum
`(2•𝒫) + 𝒫` (with the secant slope through the doubled point `2•𝒫` and the generic point `𝒫`)
equals `mulByThreeEndo h2 h3 (genX W) = Φ₃(genX)/Ψ₃(genX)²`.  Working in the rank-`2` extension
`F(x)[ψ₂]/(ψ₂² − Ψ₂Sq(x))`, the secant slope is `-a₁/2 + (Ψ₂Sq² − preΨ₄)·ψ₂/(2·Ψ₂Sq·Ψ₃)`, whose
`ψ₂`-linear part cancels in `addX`, reducing the identity to a single univariate division-polynomial
relation closed off the `b`-relation. -/
theorem addX_gen_eq_mulByThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    (W.map (algebraMap F W.FunctionField)).addX (mulByTwoEndo h2 (genX W)) (genX W)
        ((W.map (algebraMap F W.FunctionField)).slope (mulByTwoEndo h2 (genX W)) (genX W)
          (mulByTwoEndo h2 (genY W)) (genY W))
      = mulByThreeEndo h2 h3 (genX W) := by
  set W' := W.map (algebraMap F W.FunctionField) with hW'
  set x := genX W with hxdef
  set y := genY W with hydef
  set p := W'.Ψ₂Sq.eval x with hpdef
  set T := W'.Ψ₃.eval x with hTdef
  set Q := W'.preΨ₄.eval x with hQdef
  set s := 2 * y + W'.a₁ * x + W'.a₃ with hsdef
  have h2F : (2 : W.FunctionField) ≠ 0 := by
    have hinj := (algebraMap F W.FunctionField).injective
    intro h; exact h2 (hinj (by rw [map_ofNat, map_zero]; exact h))
  have hsne : s ≠ 0 := by
    have h := psiTwo_gen_ne (W := W) h2
    rw [ψ_two_evalEval] at h; rw [hsdef]; exact h
  have hs : s ^ 2 = p := by
    have hsq := ψ_sq_evalEval (W := W') equation_gen 2
    rw [ΨSq_two, ψ_two_evalEval] at hsq; rw [hsdef, hpdef]; exact hsq
  have hpne : p ≠ 0 := by rw [← hs]; exact pow_ne_zero 2 hsne
  have hTne : T ≠ 0 := by
    have h := psiThree_gen_ne (W := W) h3
    rw [ψ_evalEval equation_gen 3, Ψ_three, evalEval_C, ← hTdef] at h; exact h
  set Φ2 := (W'.Φ 2).eval x with hΦ2def
  have hΦ2 : Φ2 = x * p - T := by
    rw [hΦ2def, hpdef, hTdef, Φ_two, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃]
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_ofNat]
    ring
  set Φ3v := (W'.Φ 3).eval x with hΦ3def
  have hΦ3 : Φ3v = x * T ^ 2 - Q * p := by
    rw [hΦ3def, Φ_three]
    simp only [eval_sub, eval_mul, eval_pow, eval_X]
    rw [← hTdef, ← hQdef, ← hpdef]
  have hcore : (p ^ 2 - Q) ^ 2 + 4 * T ^ 3 - (W'.b₂ + 12 * x) * p * T ^ 2 + 4 * Q * p ^ 2 = 0 := by
    rw [hpdef, hTdef, hQdef, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄]
    simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_ofNat]
    linear_combination (W'.b₈ ^ 2 + 6 * x * W'.b₆ * W'.b₈ + 9 * x ^ 2 * W'.b₆ ^ 2 +
        8 * x ^ 2 * W'.b₄ * W'.b₈ + 24 * x ^ 3 * W'.b₄ * W'.b₆ + 4 * x ^ 3 * W'.b₂ * W'.b₈ +
        22 * x ^ 4 * W'.b₈ + 16 * x ^ 4 * W'.b₄ ^ 2 + 11 * x ^ 4 * W'.b₂ * W'.b₆ +
        54 * x ^ 5 * W'.b₆ + 14 * x ^ 5 * W'.b₂ * W'.b₄ + 60 * x ^ 6 * W'.b₄ +
        3 * x ^ 6 * W'.b₂ ^ 2 + 24 * x ^ 7 * W'.b₂ + 45 * x ^ 8) * W'.b_relation
  simp only [WeierstrassCurve.b₂] at hcore
  have hXsub : mulByTwoEndo h2 x - x = -T / p := by
    rw [mulByTwoEndo_genX, ← hpdef, ← hΦ2def, hΦ2]; field_simp; ring
  have hYsub : mulByTwoEndo h2 y - y = (Q - p ^ 2 + W'.a₁ * T * s) / (2 * p * s) := by
    rw [mulByTwoEndo_genY, ψ_two_evalEval, ← hpdef, ← hQdef, ← hΦ2def, ← hsdef, hΦ2,
      show y = (s - W'.a₁ * x - W'.a₃) / 2 from by rw [eq_div_iff h2F, hsdef]; ring]
    field_simp
    linear_combination (p * x * W'.a₁ * s - T * W'.a₁ * s - p * s ^ 2 + p * W'.a₃ * s - Q) * hs
  have hslope : W'.slope (mulByTwoEndo h2 x) x (mulByTwoEndo h2 y) y
      = -(W'.a₁) / 2 + (p ^ 2 - Q) * s / (2 * p * T) := by
    rw [slope_of_X_ne (mulByTwoEndo_genX_ne_genX h2 h3), hYsub, hXsub]
    field_simp
    linear_combination (-(p ^ 2 - Q)) * hs
  rw [hslope, mulByThreeEndo_genX, ΨSq_three]
  simp only [addX, eval_pow]
  rw [mulByTwoEndo_genX, ← hpdef, ← hΦ2def, hΦ2, ← hTdef, ← hΦ3def, hΦ3]
  field_simp
  linear_combination (p ^ 2 - Q) ^ 2 * hs + p * hcore

set_option maxHeartbeats 2000000 in
-- The tripling `y`-identity clears the doubling denominators into a large rational-function
-- identity whose `ring` normalisation needs a raised heartbeat limit.
open Classical in
omit [W.IsElliptic] in
/-- **The `y`-coordinate of the tripling formula.** The `y`-coordinate `addY` of the secant sum
`(2•𝒫) + 𝒫` equals `mulByThreeEndo h2 h3 (genY W)` — the classical `3`-division `y`-coordinate
`ω₃(genX, genY)/(2·ψ₃³)`.  With the `x`-coordinate already matched (`addX_gen_eq_mulByThree`), the
`y`-coordinate reduces to a pure rational-function identity in the doubling data. -/
theorem addY_gen_eq_mulByThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    (W.map (algebraMap F W.FunctionField)).addY (mulByTwoEndo h2 (genX W)) (genX W)
        (mulByTwoEndo h2 (genY W))
        ((W.map (algebraMap F W.FunctionField)).slope (mulByTwoEndo h2 (genX W)) (genX W)
          (mulByTwoEndo h2 (genY W)) (genY W))
      = mulByThreeEndo h2 h3 (genY W) := by
  set W' := W.map (algebraMap F W.FunctionField) with hW'
  set x := genX W with hxdef
  set y := genY W with hydef
  set p := W'.Ψ₂Sq.eval x with hpdef
  set T := W'.Ψ₃.eval x with hTdef
  set Q := W'.preΨ₄.eval x with hQdef
  set s := 2 * y + W'.a₁ * x + W'.a₃ with hsdef
  have h2F : (2 : W.FunctionField) ≠ 0 := by
    have hinj := (algebraMap F W.FunctionField).injective
    intro h; exact h2 (hinj (by rw [map_ofNat, map_zero]; exact h))
  have hsne : s ≠ 0 := by
    have h := psiTwo_gen_ne (W := W) h2
    rw [ψ_two_evalEval] at h; rw [hsdef]; exact h
  have hs : s ^ 2 = p := by
    have hsq := ψ_sq_evalEval (W := W') equation_gen 2
    rw [ΨSq_two, ψ_two_evalEval] at hsq; rw [hsdef, hpdef]; exact hsq
  have hpne : p ≠ 0 := by rw [← hs]; exact pow_ne_zero 2 hsne
  have hTne : T ≠ 0 := by
    have h := psiThree_gen_ne (W := W) h3
    rw [ψ_evalEval equation_gen 3, Ψ_three, evalEval_C, ← hTdef] at h; exact h
  set Φ2 := (W'.Φ 2).eval x with hΦ2def
  have hΦ2 : Φ2 = x * p - T := by
    rw [hΦ2def, hpdef, hTdef, Φ_two, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃]
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_ofNat]
    ring
  set Φ3v := (W'.Φ 3).eval x with hΦ3def
  have hΦ3 : Φ3v = x * T ^ 2 - Q * p := by
    rw [hΦ3def, Φ_three]
    simp only [eval_sub, eval_mul, eval_pow, eval_X]
    rw [← hTdef, ← hQdef, ← hpdef]
  set Kv := (W'.preΨ 5).eval x - Q ^ 2 with hKdef
  have hK : Kv = Q * p ^ 2 - T ^ 3 - Q ^ 2 := by
    rw [hKdef, preΨ_five]
    simp only [eval_sub, eval_mul, eval_pow]
    rw [← hpdef, ← hTdef, ← hQdef]
  have hslope : W'.slope (mulByTwoEndo h2 x) x (mulByTwoEndo h2 y) y
      = -(W'.a₁) / 2 + (p ^ 2 - Q) * s / (2 * p * T) := by
    have hXsub : mulByTwoEndo h2 x - x = -T / p := by
      rw [mulByTwoEndo_genX, ← hpdef, ← hΦ2def, hΦ2]; field_simp; ring
    have hYsub : mulByTwoEndo h2 y - y = (Q - p ^ 2 + W'.a₁ * T * s) / (2 * p * s) := by
      rw [mulByTwoEndo_genY, ψ_two_evalEval, ← hpdef, ← hQdef, ← hΦ2def, ← hsdef, hΦ2,
        show y = (s - W'.a₁ * x - W'.a₃) / 2 from by rw [eq_div_iff h2F, hsdef]; ring]
      field_simp
      linear_combination (p * x * W'.a₁ * s - T * W'.a₁ * s - p * s ^ 2 + p * W'.a₃ * s - Q) * hs
    rw [slope_of_X_ne (mulByTwoEndo_genX_ne_genX h2 h3), hYsub, hXsub]
    field_simp
    linear_combination (-(p ^ 2 - Q)) * hs
  have hY2 : mulByTwoEndo h2 y = -(W'.a₁ * Φ2 + W'.a₃ * p) / (2 * p) + Q / (2 * p ^ 2) * s := by
    rw [mulByTwoEndo_genY, ψ_two_evalEval, ← hpdef, ← hQdef, ← hΦ2def, ← hsdef]
    field_simp
    linear_combination (p * s * Φ2 * W'.a₁ + p ^ 2 * s * W'.a₃ - Q * s ^ 2 - p * Q) * hs
  rw [addY, negAddY, addX_gen_eq_mulByThree h2 h3, negY, mulByThreeEndo_genX, ΨSq_three]
  simp only [eval_pow]
  rw [hslope, mulByTwoEndo_genX, ← hpdef, ← hΦ2def, ← hTdef, hY2,
    mulByThreeEndo_genY, ψ_evalEval equation_gen 3, Ψ_three, evalEval_C, ← hTdef, ← hsdef, ← hKdef,
    ← hΦ3def, hΦ2, hΦ3, hK]
  field_simp
  ring

open Classical in
/-- **The tripling correspondence.** The multiplication-by-`3` endomorphism `mulByThreeEndo h2 h3`
acts on the coordinate generators of `F(W)` exactly as the group triple `𝒫 ↦ 𝒫 + 𝒫 + 𝒫 = [3]•𝒫` in
`(W ⁄ F(W)).Point`:

```
𝒫 + 𝒫 + 𝒫 = (mulByThreeEndo h2 h3 (genX W), mulByThreeEndo h2 h3 (genY W)).
```

The double `𝒫 + 𝒫` is the doubled point `(mulByTwoEndo genX, mulByTwoEndo genY)`
(`genericPoint_add_self`), and since `x(2•𝒫) ≠ x(𝒫)` (`mulByTwoEndo_genX_ne_genX`) the further sum
`(2•𝒫) + 𝒫` takes the secant branch `add_of_X_ne`, whose `addX`/`addY` coordinates are the
division-polynomial tripling coordinates (`addX_gen_eq_mulByThree`/`addY_gen_eq_mulByThree`).  This
is the `n = 3` mirror of `genericPoint_add_self` — the tripling slice of the bridge
`mulByNEndo = [n]•`. -/
theorem genericPoint_add_add_self (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    genericPoint + genericPoint + genericPoint
      = Point.some (mulByThreeEndo h2 h3 (genX W)) (mulByThreeEndo h2 h3 (genY W))
          (nonsingular_mulByThreeEndo_gen h2 h3) := by
  rw [show genericPoint + genericPoint
        = Point.some (mulByTwoEndo h2 (genX W)) (mulByTwoEndo h2 (genY W))
            (nonsingular_mulByTwoEndo_gen h2) from genericPoint_add_self h2,
    genericPoint, Point.add_of_X_ne (mulByTwoEndo_genX_ne_genX h2 h3), Point.some.injEq]
  exact ⟨addX_gen_eq_mulByThree h2 h3, addY_gen_eq_mulByThree h2 h3⟩


end CoordinateRing

end WeierstrassCurve.Affine
