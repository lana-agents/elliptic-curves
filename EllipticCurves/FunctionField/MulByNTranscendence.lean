/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByNPullback
import EllipticCurves.FunctionField.TranslationDoublingCommGeneral
import EllipticCurves.FunctionField.TranslationAction
import EllipticCurves.FunctionField.ConstantFieldDomain
import EllipticCurves.Torsion.TwoPrimary

/-!
# `[n]` is non-constant: discharging the hypothesis of `mulByNEndo`

`EllipticCurves.FunctionField.MulByNPullback` builds the multiplication-by-`n` endomorphism
`[n]∗ : F(W) →+* F(W)` for every `n : ℕ` out of the group multiple `n • 𝒫` of the generic point,
under the single hypothesis

```
Transcendental F (n • 𝒫).xCoord
```

— geometrically, that `[n]` is a **non-constant** map.  This file discharges that hypothesis.

## The criterion

The whole argument is one application of the translation automorphism.  If `n • 𝒫` were a constant
point `c`, then applying the `F`-algebra automorphism `τ_T∗` for a base-field point `T` — which
sends `𝒫` to `𝒫 + 𝒯` (`genPointHom_genericPoint_translate`) and fixes every constant point
(`genPointHom_translatePoint`) — gives

```
c = τ_T∗ c = τ_T∗ (n • 𝒫) = n • (𝒫 + 𝒯) = n • 𝒫 + n • 𝒯 = c + n • 𝒯,
```

so `n • 𝒯 = 0`, i.e. **every** base-field point is `n`-torsion.  Contrapositively, one base-field
point that is not `n`-torsion suffices:

* `nsmul_genericPoint_ne_torsionPointMap`, then `transcendental_xCoord_nsmul_genericPoint`.

⚠️ Turning *"the `x`-coordinate is algebraic"* into *"the point is constant"* is the second half,
and it is where the merged `algebraicClosure_functionField_eq_bot` (`ConstantFieldDomain.lean`) is
used: an `x` algebraic over `F` lies in `F`, and then the Weierstrass equation exhibits `y` as a
root of a monic quadratic over `F`, so `y` lies in `F` too.  A hypothesis on the `x`-coordinate
alone is therefore enough.

## Over an algebraically closed field the hypothesis is automatic

`E[2^k] ≃+ (ℤ/2^kℤ)²` (`nonempty_torsionTwoPow_addEquiv`, merged) supplies, for every `n ≠ 0`, a
point that is not `n`-torsion: take `k` with `2^k > n` and the point corresponding to `(1, 0)`.  So
over an algebraically closed field of characteristic `≠ 2`,

```
[n]∗ : F(W) →+* F(W) exists for every n ≠ 0,
```

with **no** use of the `y`-coordinate division polynomial `ωₙ`, of the general `n` on-curve identity
(`#404`), or of the elliptic-net recurrence (Ward, `#260`).  This is `mulByNEndoOfAlgClosed`.

## Main statements

* `…nsmul_genericPoint_ne_torsionPointMap` — `n • 𝒫` is not a constant point, given one base-field
  point that is not `n`-torsion.
* `…transcendental_xCoord_nsmul_genericPoint` — the criterion, in the form `mulByNEndo` consumes.
* `…exists_nsmul_ne_zero_of_isAlgClosed` — over `F̄` with `2 ≠ 0`, a point that is not `n`-torsion.
* `…mulByNEndoOfAlgClosed` — `[n]∗` over `F̄`, unconditionally in `n ≠ 0`.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.4.10, III.6.
-/

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

/-! ### An element algebraic over `F` is a constant -/

/-- An element of `F(W)` algebraic over `F` is a constant: `F` is relatively algebraically closed in
`F(W)` (`algebraicClosure_functionField_eq_bot`). -/
lemma exists_algebraMap_eq_of_isAlgebraic {z : W.FunctionField} (hz : IsAlgebraic F z) :
    ∃ c : F, z = algebraMap F W.FunctionField c := by
  have hmem := mem_algebraicClosure_iff.mpr hz
  rw [W.algebraicClosure_functionField_eq_bot, IntermediateField.mem_bot] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc.symm⟩

/-- **A point of `W ⁄ F(W)` with algebraic `x`-coordinate is constant.**  The `x`-coordinate is a
constant `x₀` by `exists_algebraMap_eq_of_isAlgebraic`; the Weierstrass equation then exhibits `y`
as a root of the monic quadratic `Y² + (a₁x₀ + a₃)Y − (x₀³ + a₂x₀² + a₄x₀ + a₆) ∈ F[Y]`, so `y` is
algebraic over `F` and is a constant `y₀` for the same reason.  Finally `(x₀, y₀)` lies on `W`,
because `algebraMap F F(W)` is injective. -/
lemma exists_eq_algebraMap_of_isAlgebraic_of_equation {x y : W.FunctionField}
    (h : (W.map (algebraMap F W.FunctionField)).Equation x y) (hx : IsAlgebraic F x) :
    ∃ x₀ y₀ : F, W.Equation x₀ y₀ ∧ x = algebraMap F W.FunctionField x₀ ∧
      y = algebraMap F W.FunctionField y₀ := by
  obtain ⟨x₀, hx₀⟩ := exists_algebraMap_eq_of_isAlgebraic hx
  have h' := ((W.map (algebraMap F W.FunctionField)).equation_iff x y).mp h
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at h'
  subst hx₀
  have hcoeff : (X ^ 2 + C (W.a₁ * x₀ + W.a₃) * X
      - C (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) : F[X]).coeff 2 = 1 := by
    rw [coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X]
    norm_num
  have hy : IsAlgebraic F y := by
    refine ⟨X ^ 2 + C (W.a₁ * x₀ + W.a₃) * X
        - C (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆), fun hp => ?_, ?_⟩
    · rw [hp, coeff_zero] at hcoeff; exact zero_ne_one hcoeff
    · simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C]
      linear_combination h'
  obtain ⟨y₀, hy₀⟩ := exists_algebraMap_eq_of_isAlgebraic hy
  subst hy₀
  refine ⟨x₀, y₀, ?_, rfl, rfl⟩
  rw [Affine.equation_iff]
  refine (algebraMap F W.FunctionField).injective ?_
  simp only [map_add, map_mul, map_pow]
  linear_combination h'

/-! ### The translation criterion -/

variable [W.IsElliptic]

open Classical in
/-- A base-field point maps to `0` in `(W ⁄ F(W)).Point` only if it is `0`. -/
lemma torsionPointMap_eq_zero_iff {Q : W.Point} :
    torsionPointMap (W := W) Q = 0 ↔ Q = 0 := by
  refine ⟨fun hq => ?_, fun hq => by rw [hq, map_zero]⟩
  cases Q with
  | zero => rfl
  | some x y h =>
    rw [torsionPointMap_some, translatePoint] at hq
    exact absurd hq (by simp)

open Classical in
/-- Every `F`-algebra endomorphism of `F(W)` fixes the image of the base-field points — the `0`
case of `genPointHom_translatePoint`, folded in. -/
lemma genPointHom_torsionPointMap (φ : W.FunctionField →ₐ[F] W.FunctionField) (Q : W.Point) :
    genPointHom φ (torsionPointMap Q) = torsionPointMap Q := by
  cases Q with
  | zero => rw [← Point.zero_def, map_zero, map_zero]
  | some x y h => rw [torsionPointMap_some]; exact genPointHom_translatePoint φ h.left

open Classical in
/-- **`n • 𝒫` is not a constant point**, as soon as some base-field point `T` is not `n`-torsion.

Applying the translation automorphism `τ_T∗` to the assumed equation `n • 𝒫 = 𝒬` with `𝒬` constant
gives `n • 𝒫 + n • 𝒯 = 𝒬`, hence `n • 𝒯 = 0`; and `𝒯 ↦ n • 𝒯` is the image of `T ↦ n • T` under the
injective base-change homomorphism `torsionPointMap`. -/
theorem nsmul_genericPoint_ne_torsionPointMap (n : ℕ) {T : W.Point} (hT : n • T ≠ 0)
    (Q : W.Point) : (n • genericPoint (W := W)) ≠ torsionPointMap Q := by
  intro heq
  rcases hTeq : T with _ | ⟨xT, yT, hns⟩
  · rw [hTeq, ← Point.zero_def, smul_zero] at hT; exact hT rfl
  · have key : genPointHom (translateEndoAlgHom hns.left) (n • genericPoint (W := W))
        = n • genericPoint (W := W) + n • translatePoint hns.left := by
      rw [map_nsmul, genPointHom_genericPoint_translate, nsmul_add]
    rw [heq, genPointHom_torsionPointMap, ← heq] at key
    have hzero : n • translatePoint (W := W) hns.left = 0 :=
      (add_left_cancel (a := n • genericPoint (W := W)) (by rw [add_zero]; exact key)).symm
    rw [← torsionPointMap_some hns, ← map_nsmul, torsionPointMap_eq_zero_iff] at hzero
    exact hT (by rw [hTeq]; exact hzero)

open Classical in
/-- **The criterion.**  One base-field point that is not `n`-torsion makes the `x`-coordinate of
`n • 𝒫` transcendental over `F` — which is exactly the hypothesis `mulByNEndo` takes. -/
theorem transcendental_xCoord_nsmul_genericPoint (n : ℕ) {T : W.Point} (hT : n • T ≠ 0) :
    Transcendental F (n • genericPoint (W := W)).xCoord := by
  intro hx
  have hne : n • genericPoint (W := W) ≠ 0 := fun h0 =>
    nsmul_genericPoint_ne_torsionPointMap n hT 0 (by rw [h0, map_zero])
  obtain ⟨x₀, y₀, h₀, hx0, hy0⟩ :=
    exists_eq_algebraMap_of_isAlgebraic_of_equation (Point.equation_of_ne_zero hne) hx
  refine nsmul_genericPoint_ne_torsionPointMap n hT
    (Point.some x₀ y₀ (W.equation_iff_nonsingular.mp h₀)) ?_
  rw [torsionPointMap_some, translatePoint]
  conv_lhs => rw [Point.eq_some_of_ne_zero hne]
  rw [Point.some.injEq]
  exact ⟨hx0, hy0⟩

/-! ### Over an algebraically closed field the hypothesis is automatic -/

variable [IsAlgClosed F]

open Classical in
/-- **Over `F̄` with `2 ≠ 0` there is, for every `n ≠ 0`, a point that is not `n`-torsion.**  Take
`k := n`, so `n < 2 ^ k`; the merged `E[2^k] ≃+ (ℤ/2^kℤ)²` transports `(1, 0)` to a point `T` with
`n • T ≠ 0`, since `(n : ZMod (2 ^ k)) ≠ 0`. -/
theorem exists_nsmul_ne_zero_of_isAlgClosed (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    ∃ T : W.Point, n • T ≠ 0 := by
  obtain ⟨e⟩ := nonempty_torsionTwoPow_addEquiv (W := W) h2 n
  refine ⟨(e.symm (1, 0) : W.torsion (2 ^ n)), fun hzero => ?_⟩
  have h1 : n • (e.symm (1, 0) : W.torsion (2 ^ n)) = 0 :=
    Subtype.ext (by push_cast; exact hzero)
  have h2' : n • ((1 : ZMod (2 ^ n)), (0 : ZMod (2 ^ n))) = 0 := by
    have := congrArg e h1
    rwa [map_nsmul, e.apply_symm_apply, map_zero] at this
  rw [Prod.ext_iff] at h2'
  have h3 : ((n : ℕ) : ZMod (2 ^ n)) = 0 := by
    have := h2'.1
    simpa [nsmul_eq_mul] using this
  rw [ZMod.natCast_eq_zero_iff] at h3
  exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h3) (by simpa using Nat.lt_two_pow_self)

open Classical in
/-- **Over `F̄` with `2 ≠ 0`, `[n]` is non-constant for every `n ≠ 0`.** -/
theorem transcendental_xCoord_nsmul_of_isAlgClosed (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    Transcendental F (n • genericPoint (W := W)).xCoord :=
  let ⟨_, hT⟩ := exists_nsmul_ne_zero_of_isAlgClosed (W := W) h2 hn
  transcendental_xCoord_nsmul_genericPoint n hT

open Classical in
/-- **The multiplication-by-`n` endomorphism `[n]∗ : F(W) →+* F(W)` over an algebraically closed
field of characteristic `≠ 2`, for every `n ≠ 0`** — with no `ωₙ`, no general `n` on-curve identity
and no elliptic-net recurrence. -/
noncomputable def mulByNEndoOfAlgClosed (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    W.FunctionField →+* W.FunctionField :=
  mulByNEndo n (transcendental_xCoord_nsmul_of_isAlgClosed (W := W) h2 hn)

open Classical in
/-- `[n]∗` over `F̄` sends the generic point to `n • 𝒫`. -/
theorem nsmul_genericPoint_eq_of_isAlgClosed (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    n • genericPoint (W := W)
      = Point.some (mulByNEndoOfAlgClosed h2 hn (genX W)) (mulByNEndoOfAlgClosed h2 hn (genY W))
          (nonsingular_mulByNEndo_gen n (transcendental_xCoord_nsmul_of_isAlgClosed h2 hn)) :=
  nsmul_genericPoint_eq n (transcendental_xCoord_nsmul_of_isAlgClosed h2 hn)


/-! ### Non-vacuity

Every statement above is conditional on `[IsAlgClosed F]`, `[W.IsElliptic]` and `(2 : F) ≠ 0` being
simultaneously satisfiable, and `mulByNEndoOfAlgClosed` is a `def`, so nothing so far rules out the
hypotheses being contradictory. They are certified below on this development's standard certificate
curve `y² + y = x³` over an algebraic closure of `ℚ` — the curve
`EllipticCurves.Torsion.ThreePrimary` and `EllipticCurves.Torsion.ThreePrimaryBasis` use for the
same purpose — at `n = 5`, an index beyond the merged `n = 2` and `n = 3`.

⚠️ **The superlative this sentence used to carry has been corrected** — it read *"the first index
beyond the merged `n = 2` and `n = 3`"*, and `5` is not that: `4` is.  Nothing here needs the first
such index, only one past `3`, and `5` is what the certificate below elaborates at. -/

section Nonvacuity

/-- The curve `y² + y = x³` over `ℚ`, this development's standard certificate curve. -/
private noncomputable def exampleCurveN : Affine ℚ := ⟨0, 0, 1, 0, 0⟩

/-- An algebraically closed extension of `ℚ`. -/
private abbrev exampleFieldN : Type := AlgebraicClosure ℚ

private instance : exampleCurveN.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurveN, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- ⚠️ `WeierstrassCurve.baseChange` is a plain `def`, so `[(W⁄F).IsElliptic]` is **not** found by
bare `inferInstance` from `[W.IsElliptic]`. -/
private instance : (exampleCurveN⁄exampleFieldN).IsElliptic :=
  inferInstanceAs (exampleCurveN.map (algebraMap ℚ exampleFieldN)).IsElliptic

private lemma exampleTwoN : (2 : exampleFieldN) ≠ 0 := by norm_num

open Classical in
/-- **⚠️ THE CERTIFICATE, part one.** On a curve that exists, the generic point is genuinely not
`5`-torsion — `5` being an index beyond the merged `n = 2` and `n = 3`. -/
example : (5 : ℕ) • genericPoint (W := exampleCurveN⁄exampleFieldN) ≠ 0 :=
  ne_zero_of_transcendental_xCoord
    (transcendental_xCoord_nsmul_of_isAlgClosed exampleTwoN (by norm_num))

open Classical in
/-- **⚠️ THE CERTIFICATE, part two.** On the same curve, `[5]∗` is a genuine injective endomorphism
of the function field. -/
example : Function.Injective
    (mulByNEndoOfAlgClosed (W := exampleCurveN⁄exampleFieldN) exampleTwoN (n := 5)
      (by norm_num)) :=
  mulByNEndo_injective _ _

open Classical in
/-- **⚠️ THE CERTIFICATE, part three.** And it is the *right* endomorphism: it sends the generic
`x`-coordinate to the `x`-coordinate of `5 • 𝒫`. -/
example : mulByNEndoOfAlgClosed (W := exampleCurveN⁄exampleFieldN) exampleTwoN (n := 5)
      (by norm_num) (genX (exampleCurveN⁄exampleFieldN))
    = ((5 : ℕ) • genericPoint (W := exampleCurveN⁄exampleFieldN)).xCoord :=
  mulByNEndo_genX _ _

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
