/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FormalGroup.GroupLawBaseSlice

/-!
# The pole-cleared invariant differential and its substitution along the group law

This file develops the algebraic infrastructure behind the **invariant-differential invariance**
`(★)` of Silverman AEC IV.5, Proposition 5.2:

`(★)  (ω_E ∘ F)·∂_{z₂}F = ω_E(z₂)`   in `MvPowerSeries (Fin 2) R` (over a `ℚ`-algebra),

where `ω_E = W.invariantDifferential`, `F = W.formalGroupZW`, `∂_{z₂} = MvPowerSeries.pderivSnd`.
`(★)` is exactly the hypothesis `hstar` of
`WeierstrassCurve.formalLog_subst_formalGroupZW_of_star`
(`EllipticCurves.FormalGroup.GroupLawBaseSlice`), which together with the base identity
`F(z₁, 0) = z₁` yields the full log-additivity
`log_E(F) = log_E(z₁) + log_E(z₂)`.

## What this file provides (all sorry-free)

* **Step 1 — the pole-cleared invariant differential (`Eq.Ω`).**
  `WeierstrassCurve.invariantDifferential_mul_clear` :
  `ω_E · (w·(-2 + a₁z + a₃w)) = w − z·w'`   in `R⟦z⟧`, with `w = W.formalW`.
  This clears the `z³` pole of the defining identity
  `invariantDifferential_mul_invDiffDen : ω_E · invDiffDen = invDiffNum`
  (`EllipticCurves.FormalGroup.Logarithm`), using `w = z³·v` (`formalW_eq_X_pow_mul_wCofactor`)
  and the product/power rule for `PowerSeries.derivativeFun`.  It needs only the univariate
  coordinate series, not the bivariate group law.

* **Step 2 — the substituted forms (`Eq.Ω_F`, `Eq.A`).**  Substituting `Eq.Ω` along
  `F = W.formalGroupZW` (which has zero constant coefficient, so `PowerSeries.HasSubst F`) and
  multiplying by `∂_{z₂}F`, using the substitution chain rule
  `MvPowerSeries.pderivSnd_subst`:
  * `WeierstrassCurve.invariantDifferential_mul_clear_subst` (`Eq.Ω_F`) :
    `(ω_E ∘ F)·(WF·(-2 + a₁F + a₃WF)) = WF − F·(w'∘F)`, where `WF = w ∘ F`;
  * `WeierstrassCurve.invariantDifferential_mul_clear_subst_mul_pderivSnd` (`Eq.A`) :
    `(ω_E ∘ F)·∂_{z₂}F·(WF·(-2 + a₁F + a₃WF)) = WF·∂_{z₂}F − F·∂_{z₂}WF`,
    where the chain rule has folded `(w'∘F)·∂_{z₂}F` into `∂_{z₂}WF = ∂_{z₂}(w ∘ F)`.

## The frontier: `(★)` itself

`Eq.A` reduces `(★)` `(ω_E ∘ F)·∂_{z₂}F = ω_E(z₂)` to the polynomial identity

`POLY-★  WF·∂_{z₂}F − F·∂_{z₂}WF = ω_E(z₂)·(WF·(-2 + a₁F + a₃WF))`

(indeed the left-hand side of `POLY-★` is precisely the right-hand side of `Eq.A`, and cancelling
the factor `WF·(-2 + a₁F + a₃WF)` recovers `(★)`; the factor `-2 + a₁F + a₃WF` is a unit and
`WF = F³·(v ∘ F)` with `v ∘ F` a unit, so only the `F³` order-`3` factor obstructs cancellation).

`POLY-★` is **not** provable by a local `ring`/`linear_combination` combination of the curve
equations at `(F, WF)` (the fixed-point relation `formalW_subst_formalGroupZW_fixed` and its
`pderivSnd`).  It encodes *translation invariance* of the invariant differential: the `F`-trace of
`ω_E` is a translate of the `z₂`-fibre, whose own `Eq.Ω` form carries the *different* denominator
`w₂·(-2 + a₁z₂ + a₃w₂)` with `w₂ = w ∘ (X 1)`, not `WF`.  The clean Silverman IV.4.2 proof
differentiates the associativity `F(F(z₁,z₂),z₃) = F(z₁,F(z₂,z₃))`, but associativity of
`W.formalGroupZW` is still unproven downstream (issue #263), so `(★)` cannot yet be closed here.

Once associativity (`#263`) lands, `POLY-★` — hence `(★)` = the hypothesis `hstar` — closes, and
`WeierstrassCurve.formalLog_subst_formalGroupZW_of_star` delivers the unconditional
log-additivity `log_E(F) = log_E(z₁) + log_E(z₂)`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4, Theorem 4.2; IV.5,
  Proposition 5.2.
-/

namespace WeierstrassCurve

open PowerSeries

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### Step 1: the pole-cleared invariant differential `Eq.Ω` -/

/-- The formal derivative of `z³` is `3z²`. -/
private theorem derivativeFun_X_pow_three :
    derivativeFun (X ^ 3 : R⟦X⟧) = 3 * X ^ 2 := by
  have h := PowerSeries.derivative_pow R (X : R⟦X⟧) 3
  rw [PowerSeries.derivative_X, mul_one] at h
  rw [show derivativeFun (X ^ 3 : R⟦X⟧) = PowerSeries.derivative R (X ^ 3) from rfl, h]
  norm_num

/-- **Step 1 (`Eq.Ω`).** The pole-cleared defining identity of the invariant differential:
`ω_E · (w·(-2 + a₁z + a₃w)) = w − z·w'` in `R⟦z⟧`, with `w = W.formalW`.

Starting from `invariantDifferential_mul_invDiffDen : ω_E · invDiffDen = invDiffNum` and multiplying
by `z³`, both cofactors clear their `z³` pole: `z³·invDiffDen = w·(-2 + a₁z + a₃w)` (using
`w = z³·v`, `v = W.wCofactor`) and `z³·invDiffNum = w − z·w'` (using
`w' = z³·v' + 3z²·v`). -/
theorem invariantDifferential_mul_clear [Algebra ℚ R] :
    W.invariantDifferential * (W.formalW * (-2 + C W.a₁ * X + C W.a₃ * W.formalW))
      = W.formalW - X * derivativeFun W.formalW := by
  have hderiv : derivativeFun W.formalW
      = X ^ 3 * derivativeFun W.wCofactor + 3 * X ^ 2 * W.wCofactor := by
    conv_lhs => rw [W.formalW_eq_X_pow_mul_wCofactor]
    rw [derivativeFun_mul, smul_eq_mul, smul_eq_mul, derivativeFun_X_pow_three]
    ring
  have ha : X ^ 3 * W.invDiffDen = W.formalW * (-2 + C W.a₁ * X + C W.a₃ * W.formalW) := by
    rw [invDiffDen, ← mul_assoc, ← W.formalW_eq_X_pow_mul_wCofactor]
  have hb : X ^ 3 * W.invDiffNum = W.formalW - X * derivativeFun W.formalW := by
    rw [invDiffNum, hderiv, W.formalW_eq_X_pow_mul_wCofactor]
    ring
  calc W.invariantDifferential * (W.formalW * (-2 + C W.a₁ * X + C W.a₃ * W.formalW))
      = W.invariantDifferential * (X ^ 3 * W.invDiffDen) := by rw [ha]
    _ = W.invariantDifferential * W.invDiffDen * X ^ 3 := by ring
    _ = W.invDiffNum * X ^ 3 := by rw [W.invariantDifferential_mul_invDiffDen]
    _ = X ^ 3 * W.invDiffNum := by ring
    _ = W.formalW - X * derivativeFun W.formalW := hb

/-! ### Step 2: substitution along the group law `F` -/

/-- **Step 2 (`Eq.Ω_F`).** The pole-cleared identity `Eq.Ω` substituted along `F = W.formalGroupZW`.
Writing `WF = w ∘ F = W.formalW.subst F`,
`(ω_E ∘ F)·(WF·(-2 + a₁F + a₃WF)) = WF − F·(w' ∘ F)`.
Obtained by applying the substitution algebra homomorphism `PowerSeries.substAlgHom` for `F` to
`invariantDifferential_mul_clear`; `F` is substitutable since its constant coefficient vanishes
(`hasSubst_formalGroupZW`). -/
theorem invariantDifferential_mul_clear_subst [Algebra ℚ R] :
    W.invariantDifferential.subst W.formalGroupZW
        * (W.formalW.subst W.formalGroupZW
          * (-2 + MvPowerSeries.C W.a₁ * W.formalGroupZW
            + MvPowerSeries.C W.a₃ * W.formalW.subst W.formalGroupZW))
      = W.formalW.subst W.formalGroupZW
        - W.formalGroupZW * W.formalW.derivativeFun.subst W.formalGroupZW := by
  have hG := W.hasSubst_formalGroupZW
  have key := congrArg (PowerSeries.substAlgHom hG) W.invariantDifferential_mul_clear
  simp only [map_mul, map_add, map_neg, map_sub, map_ofNat] at key
  simp only [PowerSeries.coe_substAlgHom hG, PowerSeries.subst_C, PowerSeries.subst_X hG] at key
  exact key

/-- **Step 2 (`Eq.A`).** `Eq.Ω_F` multiplied by `∂_{z₂}F`, with the chain rule
`MvPowerSeries.pderivSnd_subst` folding `(w' ∘ F)·∂_{z₂}F` into `∂_{z₂}(w ∘ F)`:
`(ω_E ∘ F)·∂_{z₂}F·(WF·(-2 + a₁F + a₃WF)) = WF·∂_{z₂}F − F·∂_{z₂}WF`, with `WF = w ∘ F`.

Its right-hand side is the left-hand side of the polynomial frontier `POLY-★`; this is as far as the
purely local `(z, w)` structure reaches towards the invariance `(★)`. -/
theorem invariantDifferential_mul_clear_subst_mul_pderivSnd [Algebra ℚ R] :
    W.invariantDifferential.subst W.formalGroupZW * MvPowerSeries.pderivSnd W.formalGroupZW
        * (W.formalW.subst W.formalGroupZW
          * (-2 + MvPowerSeries.C W.a₁ * W.formalGroupZW
            + MvPowerSeries.C W.a₃ * W.formalW.subst W.formalGroupZW))
      = W.formalW.subst W.formalGroupZW * MvPowerSeries.pderivSnd W.formalGroupZW
        - W.formalGroupZW
          * MvPowerSeries.pderivSnd (W.formalW.subst W.formalGroupZW) := by
  have hΩF := W.invariantDifferential_mul_clear_subst
  have hchain := MvPowerSeries.pderivSnd_subst W.constantCoeff_formalGroupZW W.formalW
  linear_combination MvPowerSeries.pderivSnd W.formalGroupZW * hΩF + W.formalGroupZW * hchain

end WeierstrassCurve
