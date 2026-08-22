/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.PlacePullback

/-!
# `[2]` fixes the point at infinity, and is unramified there

`EllipticCurves.FunctionField.PlacePullback` pulls places of `F(W)` back along a non-invertible
`F`-embedding `φ`, producing a contraction `comapProjPoint φ` and a ramification index, and
instantiates both at `φ = mulByTwoEndo h2`:

```
divisorProj_mulByTwoEndo_apply :
    divisorProj W (mulByTwoEndo h2 f) p
      = ramificationIdxTwo h2 p * divisorProj W f (comapProjPointTwo h2 p).
```

Its docstring says, correctly, that nothing there *computes* either the contraction or the index.
This file computes both at the one point where every downstream consumer needs them: the point at
infinity.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.ordInfty_mulByTwoEndo_genX` —
  `ordInfty W (mulByTwoEndo h2 (genX W)) = -2`: the pullback of the generic `x`-coordinate along
  `[2]` still has a double pole at infinity.  This one degree computation carries the whole file.
* `WeierstrassCurve.Affine.CoordinateRing.comapProjPointTwo_none` —
  **`[2]` fixes the point at infinity**: `comapProjPointTwo h2 none = none`.  Classically, `[2]`
  extends to a morphism of the projective curve sending `O` to `O`; this is the first time this
  tree can say it.
* `WeierstrassCurve.Affine.CoordinateRing.ramificationIdxTwo_none` — **`[2]` is unramified at
  infinity**: `ramificationIdxTwo h2 none = 1`.
* `WeierstrassCurve.Affine.CoordinateRing.divisorProj_mulByTwoEndo_apply_none` and
  `ordInfty_mulByTwoEndo` — the payoff a consumer reaches for:
  `ordInfty W (f ∘ [2]) = ordInfty W f` for `f ≠ 0`.

## Both conclusions come out of one equation

Write `q := comapProjPointTwo h2 none` and `e := ramificationIdxTwo h2 none`, and run the transport
equation *backwards* at `f = genX W`, `p = none`:

```
-2 = ordInfty (genX ∘ [2]) = divisorProj W (genX ∘ [2]) none = e * divisorProj W (genX W) q.
```

`genX W` lies in the image of the coordinate ring, so `0 ≤ ord v (genX W)` at every affine place
`v` (`ord_algebraMap_nonneg`); with `0 < e` the right-hand side would then be nonnegative.  Hence
`q = none`, and `divisorProj W (genX W) none = -2` turns the same equation into `e * (-2) = -2`,
i.e. `e = 1`.  No case analysis beyond the two constructors of `Option`, and in particular no
direct comparison of valuation subrings — `f ∈ O_∞ ↔ φ f ∈ O_∞` in both directions is the
expensive route and it is not needed.

## Where the characteristic hypothesis becomes load-bearing

`mulByTwoEndo` carries `h2 : (2 : F) ≠ 0` in its signature, so it is tempting to read `h2` here as
inherited.  It is not: the degree computation needs `natDegree W.Ψ₂Sq = 3` **exactly**, and
`Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆` has leading coefficient `4`, which is nonzero precisely because
`(2 : F) ≠ 0`.  A `≤` bound is not enough — both degrees have to be equalities for the difference
`-8 - (-6)` to come out.

Mathlib already provides both exact degrees (`WeierstrassCurve.natDegree_Φ` for `Nontrivial R`, and
`WeierstrassCurve.natDegree_Ψ₂Sq` under `(4 : R) ≠ 0`), so no new degree lemma is proved here; only
the passage from `q(genX)` to the coordinate-ring class `mk W (C q)` is.

## What is *not* here

* **`ramificationIdxTwo` at an affine point.**  Nothing below says `[2]` is unramified anywhere
  other than at infinity.  ⚠️ Earlier wording continued "and it is not: it ramifies at the
  `2`-torsion points", which is **false**:
  `EllipticCurves.FunctionField.MulByTwoFibreInfinity` (`#774`) computes
  `ramificationIdxTwo h2 (some (pointClosedPoint h)) = 1` at every affine `2`-torsion point over an
  algebraically closed base field.  What ramifies there is the degree-`4` map `x ∘ [2] : ℙ¹ → ℙ¹`
  — which is exactly the `Ψ₂Sq` vanishing this file exploits — and not `[2] : E → E`, a separable
  isogeny.  Indices at a place lying over an *affine* place are still computed nowhere.
* **The degree formula `∑_{p ↦ q} e_p · deg p = 4`.**  That needs finiteness of the fibres of
  `comapProjPointTwo`, which is not in this tree; it is also what `pullbackDivisor` as a map of
  `Finsupp`s (`#414`/`#422` deliverable 1) waits on.
* `[3]∗`.  The argument transposes verbatim once `MulByThree*` supplies the two hypotheses of
  `comapProjPoint`, with `natDegree (Φ 3) = 9` and `natDegree (ΨSq 3) = 8` in place of `4` and `3`.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], II.2 (a morphism of curves is
  finite and surjective), III.4 (the multiplication-by-`n` map).
-/

open Polynomial

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

/-! ### Polynomials in the generic `x`-coordinate

The generic point evaluates a base-changed univariate polynomial to the image of a coordinate-ring
class, whose order at infinity the merged `deg` calculus already knows. -/

/-- **Evaluating at the generic `x`-coordinate is taking a coordinate-ring class.** For `q : F[X]`,
the value of the base-changed polynomial `q.map (F → F(W))` at `genX W` is the image in `F(W)` of
the class of the constant bivariate polynomial `C q`. -/
lemma genPsi_mk_C_eq_eval_map (q : F[X]) :
    genPsi W (mk W (C q)) = (q.map (algebraMap F W.FunctionField)).eval (genX W) := by
  rw [genPsi_mk_map_evalEval, Polynomial.map_C, coe_mapRingHom, evalEval_C]

/-- A nonzero polynomial does not vanish at the generic `x`-coordinate: `genX W` is transcendental
over `F`. -/
lemma eval_map_genX_ne_zero {q : F[X]} (hq : q ≠ 0) :
    (q.map (algebraMap F W.FunctionField)).eval (genX W) ≠ 0 := by
  rw [← genPsi_mk_C_eq_eval_map]
  exact fun h => mk_C_ne_zero hq
    ((injective_iff_map_eq_zero _).mp
      (IsFractionRing.injective W.CoordinateRing W.FunctionField) _ h)

/-- **The order at infinity of `q(genX)` is `-2 · deg q`.** A polynomial of degree `d` in the
generic `x`-coordinate has a pole of order `2d` at infinity, because `x` itself has a double
pole. -/
lemma ordInfty_eval_map_genX {q : F[X]} (hq : q ≠ 0) :
    ordInfty W ((q.map (algebraMap F W.FunctionField)).eval (genX W))
      = -(2 * q.natDegree : ℤ) := by
  rw [← genPsi_mk_C_eq_eval_map, genPsi, ordInfty_algebraMap (mk_C_ne_zero hq), deg_mk_C]
  push_cast
  ring

/-! ### The order at infinity of `x ∘ [2]` -/

/-- The scalar `4` is nonzero when `2` is: this is what makes `Ψ₂Sq` a genuine cubic. -/
private lemma four_ne_zero_of_two_ne_zero (h2 : (2 : F) ≠ 0) : (4 : F) ≠ 0 := by
  have h : (4 : F) = 2 * 2 := by norm_num
  rw [h]
  exact mul_ne_zero h2 h2

/-- **`ordInfty (x ∘ [2]) = -2`.** The duplication formula writes `x(2P) = Φ₂(x)/Ψ₂Sq(x)` with
`natDegree (Φ 2) = 4` and `natDegree Ψ₂Sq = 3`, so the pole orders at infinity are `8` and `6` and
the quotient has a double pole — the same order as `x` itself.

The exact degree of `Ψ₂Sq` needs its leading coefficient `4` to be nonzero, which is where
`h2 : (2 : F) ≠ 0` stops being inherited from `mulByTwoEndo` and starts doing work. -/
theorem ordInfty_mulByTwoEndo_genX (h2 : (2 : F) ≠ 0) :
    ordInfty W (mulByTwoEndo h2 (genX W)) = -2 := by
  have h4 : (4 : F) ≠ 0 := four_ne_zero_of_two_ne_zero h2
  have hΦ : ((W.map (algebraMap F W.FunctionField)).Φ 2)
      = (W.Φ 2).map (algebraMap F W.FunctionField) := map_Φ ..
  have hΨ : ((W.map (algebraMap F W.FunctionField)).Ψ₂Sq)
      = W.Ψ₂Sq.map (algebraMap F W.FunctionField) := map_Ψ₂Sq ..
  rw [mulByTwoEndo_genX h2, hΦ, hΨ,
    ordInfty_div (eval_map_genX_ne_zero (W.Φ_ne_zero 2))
      (eval_map_genX_ne_zero (W.Ψ₂Sq_ne_zero h4)),
    ordInfty_eval_map_genX (W.Φ_ne_zero 2), ordInfty_eval_map_genX (W.Ψ₂Sq_ne_zero h4),
    W.natDegree_Φ 2, W.natDegree_Ψ₂Sq h4]
  decide

/-! ### The contraction and the index at infinity -/

variable [IsDedekindDomain W.CoordinateRing]

/-- **`[2]` fixes the point at infinity.**  The contraction of the place at infinity along `[2]∗` is
the place at infinity: `comapProjPointTwo h2 none = none`.

Classically this is the statement that multiplication by `2` extends to a morphism of the
projective curve carrying `O` to `O`.  The proof runs `divisorProj_mulByTwoEndo_apply` backwards at
the generic `x`-coordinate: an affine contraction would make the right-hand side a nonnegative
multiple of a nonnegative order, but the left-hand side is `-2`. -/
theorem comapProjPointTwo_none (h2 : (2 : F) ≠ 0) :
    comapProjPointTwo h2 (none : ProjPoint W) = none := by
  have hkey : (-2 : ℤ) = ramificationIdxTwo h2 (none : ProjPoint W)
      * divisorProj W (genX W) (comapProjPointTwo h2 (none : ProjPoint W)) := by
    rw [← divisorProj_mulByTwoEndo_apply h2 genX_ne_zero none, divisorProj_apply_none,
      ordInfty_mulByTwoEndo_genX h2]
  cases hq : comapProjPointTwo h2 (none : ProjPoint W) with
  | none => rfl
  | some v =>
    exfalso
    rw [hq, divisorProj_apply_some] at hkey
    have hge : (0 : ℤ) ≤ ord v (genX W) := by
      rw [genX, genPsi]
      exact ord_algebraMap_nonneg v _
    have hnn : (0 : ℤ) ≤ ramificationIdxTwo h2 (none : ProjPoint W) * ord v (genX W) :=
      mul_nonneg (ramificationIdxTwo_pos h2 none).le hge
    linarith

/-- **`[2]` is unramified at the point at infinity**: `ramificationIdxTwo h2 none = 1`.

Note what this is *not*: it is not `deg [2] = 4`, and nothing here says anything about an affine
place.  ⚠️ Earlier wording added that `[2]` "really does ramify, at the `2`-torsion points"; that is
**false** — `EllipticCurves.FunctionField.MulByTwoFibreInfinity` (`#774`) computes the index `1`
there.  Indices at a place lying over an *affine* place remain uncomputed. -/
theorem ramificationIdxTwo_none (h2 : (2 : F) ≠ 0) :
    ramificationIdxTwo h2 (none : ProjPoint W) = 1 := by
  have hkey := divisorProj_mulByTwoEndo_apply h2 (f := genX W) genX_ne_zero none
  rw [comapProjPointTwo_none h2, divisorProj_apply_none, divisorProj_apply_none,
    ordInfty_mulByTwoEndo_genX h2, ordInfty_genX] at hkey
  omega

/-- **The projective payoff.**  Pulling back along `[2]` leaves the coefficient of the divisor at
the point at infinity unchanged. -/
theorem divisorProj_mulByTwoEndo_apply_none (h2 : (2 : F) ≠ 0) {f : W.FunctionField} (hf : f ≠ 0) :
    divisorProj W (mulByTwoEndo h2 f) (none : ProjPoint W) = divisorProj W f none := by
  rw [divisorProj_mulByTwoEndo_apply h2 hf, comapProjPointTwo_none h2, ramificationIdxTwo_none h2,
    one_mul]

/-- **`ordInfty (f ∘ [2]) = ordInfty f`.**  The same statement in the language of
`EllipticCurves.FunctionField.PlaceAtInfinity`: the order at infinity is a `[2]∗`-invariant.

The Dedekind hypothesis does not appear in the statement but is used in the proof, which goes
through the place-theoretic contraction. -/
theorem ordInfty_mulByTwoEndo (h2 : (2 : F) ≠ 0) {f : W.FunctionField} (hf : f ≠ 0) :
    ordInfty W (mulByTwoEndo h2 f) = ordInfty W f := by
  have h := divisorProj_mulByTwoEndo_apply_none h2 hf
  rwa [divisorProj_apply_none, divisorProj_apply_none] at h

/-! ### Non-vacuity: the statements have content on a real curve

Every theorem above carries `[IsDedekindDomain W.CoordinateRing]`, and `comapProjPointTwo` is
built from a choice principle, so it is worth exhibiting a curve on which the whole chain
elaborates with every instance discharged.  `y² = x³ - x` over `ℚ` has discriminant `64`, and the
Dedekind instance is reached from `IsElliptic` alone — no algebraically closed base field is
needed. -/

section Nonvacuity

/-- The curve `y² = x³ - x` over `ℚ`, of discriminant `64`. -/
private def exampleCurve : Affine ℚ := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

example : IsDedekindDomain exampleCurve.CoordinateRing := inferInstance

example : ordInfty exampleCurve (mulByTwoEndo (W := exampleCurve) (by norm_num) (genX _)) = -2 :=
  ordInfty_mulByTwoEndo_genX _

example : comapProjPointTwo (W := exampleCurve) (by norm_num) (none : ProjPoint exampleCurve)
    = none :=
  comapProjPointTwo_none _

example : ramificationIdxTwo (W := exampleCurve) (by norm_num) (none : ProjPoint exampleCurve)
    = 1 :=
  ramificationIdxTwo_none _

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
