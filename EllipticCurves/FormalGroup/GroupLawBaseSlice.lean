/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FormalGroup.GenuineLaw
import EllipticCurves.FormalGroup.LogAdditivity
import EllipticCurves.FormalGroup.DividedDifference
import EllipticCurves.FormalGroup.Expansion

/-!
# The base identity `F(z₁, 0) = z₁` of the genuine `(z, w)` formal group law

This file proves the formal-group **identity axiom** for the genuine bivariate law
`W.formalGroupZW : MvPowerSeries (Fin 2) R` of `EllipticCurves.FormalGroup.GenuineLaw`, namely that
its `z₂ = 0` slice is the inner variable `z₁`:

`WeierstrassCurve.finTwoEvalSndZero_formalGroupZW : finTwoEvalSndZero W.formalGroupZW = X`,

i.e. `F(z₁, 0) = z₁`.  This is the base fact `hF` required by the log-additivity reduction
`WeierstrassCurve.formalLog_subst_formalGroupZW_of_identity_star` of
`EllipticCurves.FormalGroup.LogAdditivity` (Silverman AEC IV.5, Proposition 5.2), one of whose two
hypotheses it discharges (`formalLog_subst_formalGroupZW_of_star`).

## Strategy

Write `φ := MvPowerSeries.finTwoEvalSndZero : MvPowerSeries (Fin 2) R →+* R⟦z₁⟧`, the ring
homomorphism that sends `z₁ = X 0 ↦ X`, `z₂ = X 1 ↦ 0`, `C a ↦ C a`.  Pushing `φ` through the
whole `formalGroupZW` construction (mirroring `EllipticCurves.FormalGroup.GenuineLawIdentification`,
does the same for the Laurent writer `embedDoubleLaurent`) reduces the identity to univariate power
series algebra:

* the **slope slice** `φ(λ)·X = w` (`finTwoEvalSndZero_formalWDividedDiff_mul_X`), from
  `formalWDividedDiff_spec`;
* the **intercept slice** `φ(ν) = 0` (`finTwoEvalSndZero_formalGroupNu`);
* the **root relation** `φ(A)·X² + φ(B)·X = φ(λ)` (`finTwoEvalSndZero_quadratic`), got by
  applying `φ` to `formalCubicResidual_root_zero`, substituting `w = φ(λ)·X`, and cancelling the
  non-zero-divisor `X`;
* finally the negation-series algebra, cleared of the unit denominators `A = formalGroupLead` and
  `D = formalGroupDen`, yields `φ(F) = X`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1; IV.5,
  Proposition 5.2.
-/

open MvPowerSeries

namespace MvPowerSeries

variable {R : Type*} [CommRing R]

/-- `φ(C a) = C a`: the `z₂ ↦ 0` evaluation sends the constant series to the constant series. -/
@[simp]
theorem finTwoEvalSndZero_C (a : R) :
    finTwoEvalSndZero (MvPowerSeries.C a : MvPowerSeries (Fin 2) R) = PowerSeries.C a := by
  refine PowerSeries.ext fun k => ?_
  rw [coeff_finTwoEvalSndZero, MvPowerSeries.coeff_C, PowerSeries.coeff_C]
  by_cases hk : k = 0
  · subst hk; simp
  · rw [if_neg (Finsupp.single_ne_zero.mpr hk), if_neg hk]

/-- The constant coefficient of `φ x` is the constant coefficient of `x`. -/
theorem constantCoeff_finTwoEvalSndZero (φ : MvPowerSeries (Fin 2) R) :
    PowerSeries.constantCoeff (finTwoEvalSndZero φ) = MvPowerSeries.constantCoeff φ := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_finTwoEvalSndZero,
    show (Finsupp.single (0 : Fin 2) 0) = 0 by simp,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- The `z₂ ↦ 0` slice of the inner embedding `f(z₁) = f.toMvPowerSeries 0` is `f`. -/
theorem finTwoEvalSndZero_toMvPowerSeries_zero (f : PowerSeries R) :
    finTwoEvalSndZero (f.toMvPowerSeries (0 : Fin 2)) = f := by
  refine PowerSeries.ext fun k => ?_
  rw [coeff_finTwoEvalSndZero, PowerSeries.coeff_toMvPowerSeries_single]

/-- The `z₂ ↦ 0` slice of the outer embedding `f(z₂) = f.toMvPowerSeries 1` is the constant
`C (constantCoeff f)`. -/
theorem finTwoEvalSndZero_toMvPowerSeries_one (f : PowerSeries R) :
    finTwoEvalSndZero (f.toMvPowerSeries (1 : Fin 2))
      = PowerSeries.C (PowerSeries.constantCoeff f) := by
  refine PowerSeries.ext fun k => ?_
  rw [coeff_finTwoEvalSndZero, PowerSeries.coeff_C]
  by_cases hk : k = 0
  · subst hk
    rw [if_pos rfl, show (Finsupp.single (0 : Fin 2) 0) = Finsupp.single 1 0 by simp,
      PowerSeries.coeff_toMvPowerSeries_single, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · rw [if_neg hk]
    refine PowerSeries.coeff_toMvPowerSeries_of_ne _ _ (fun hcon => hk ?_)
    have := congrArg (fun g => g 0) hcon
    simpa using this

end MvPowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### Constant coefficients of the `(z, w)` addition data (unit witnesses)

These re-derive the (private) constant-coefficient facts of `GenuineLaw.lean` needed to invert the
unit denominators `A = formalGroupLead` and `D = formalGroupDen`. -/

private lemma cc_formalWDividedDiff :
    MvPowerSeries.constantCoeff W.formalWDividedDiff = 0 :=
  MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mp
    (le_trans (by exact_mod_cast one_le_two) W.two_le_order_formalWDividedDiff)

private lemma cc_toMvPowerSeries_formalW_zero :
    MvPowerSeries.constantCoeff (W.formalW.toMvPowerSeries (0 : Fin 2)) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      show (0 : Fin 2 →₀ ℕ) = Finsupp.single (0 : Fin 2) 0 by simp,
      PowerSeries.coeff_toMvPowerSeries_single]
  exact PowerSeries.coeff_of_lt_order 0 (lt_of_lt_of_le (by norm_num) W.order_formalW)

private lemma cc_formalGroupNu : MvPowerSeries.constantCoeff W.formalGroupNu = 0 := by
  rw [formalGroupNu, map_sub, map_mul, W.cc_formalWDividedDiff, W.cc_toMvPowerSeries_formalW_zero]
  simp

private lemma cc_formalGroupLead : MvPowerSeries.constantCoeff W.formalGroupLead = 1 := by
  rw [formalGroupLead]
  simp only [map_add, map_mul, map_pow, MvPowerSeries.constantCoeff_C, map_one,
    W.cc_formalWDividedDiff]
  ring

private lemma cc_formalGroupSub : MvPowerSeries.constantCoeff W.formalGroupSub = 0 := by
  rw [formalGroupSub]
  simp [map_add, map_mul, map_pow, MvPowerSeries.constantCoeff_C, W.cc_formalWDividedDiff,
    W.cc_formalGroupNu]

private lemma cc_formalThirdRoot : MvPowerSeries.constantCoeff W.formalThirdRoot = 0 := by
  rw [formalThirdRoot]
  simp [map_sub, map_neg, map_mul, MvPowerSeries.constantCoeff_X, W.cc_formalGroupSub]

private lemma cc_formalGroupDen : MvPowerSeries.constantCoeff W.formalGroupDen = 1 := by
  rw [formalGroupDen]
  simp [map_sub, map_mul, map_add, map_one, MvPowerSeries.constantCoeff_C,
    W.cc_formalThirdRoot, W.cc_formalWDividedDiff, W.cc_formalGroupNu]

/-! ### The slope, intercept and cubic-coefficient slices -/

/-- **The slope slice** `φ(λ)·X = w`: the `z₂ = 0` evaluation of the divided-difference regularity
`(z₂ − z₁)·λ = w(z₂) − w(z₁)`. -/
theorem finTwoEvalSndZero_formalWDividedDiff_mul_X :
    finTwoEvalSndZero W.formalWDividedDiff * PowerSeries.X = W.formalW := by
  have hw0 : PowerSeries.constantCoeff W.formalW = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact PowerSeries.coeff_of_lt_order 0 (lt_of_lt_of_le (by norm_num) W.order_formalW)
  have hspec := congrArg finTwoEvalSndZero W.formalWDividedDiff_spec
  rw [map_mul, map_sub, map_sub, finTwoEvalSndZero_X_zero, finTwoEvalSndZero_X_one,
    finTwoEvalSndZero_toMvPowerSeries_zero, finTwoEvalSndZero_toMvPowerSeries_one, hw0,
    map_zero] at hspec
  linear_combination -hspec

/-- **The intercept slice** `φ(ν) = 0`: since `φ(λ)·X = w`, the intercept `ν = w(z₁) − λ z₁`
vanishes at `z₂ = 0`. -/
theorem finTwoEvalSndZero_formalGroupNu :
    finTwoEvalSndZero W.formalGroupNu = 0 := by
  rw [formalGroupNu, map_sub, map_mul, finTwoEvalSndZero_toMvPowerSeries_zero,
    finTwoEvalSndZero_X_zero, W.finTwoEvalSndZero_formalWDividedDiff_mul_X, sub_self]

/-- `φ(A) = 1 + a₂ φ(λ) + a₄ φ(λ)² + a₆ φ(λ)³`. -/
theorem finTwoEvalSndZero_formalGroupLead :
    finTwoEvalSndZero W.formalGroupLead
      = 1 + PowerSeries.C W.a₂ * finTwoEvalSndZero W.formalWDividedDiff
        + PowerSeries.C W.a₄ * finTwoEvalSndZero W.formalWDividedDiff ^ 2
        + PowerSeries.C W.a₆ * finTwoEvalSndZero W.formalWDividedDiff ^ 3 := by
  simp only [formalGroupLead, map_add, map_mul, map_pow, map_one, finTwoEvalSndZero_C]

/-- `φ(B) = a₁ φ(λ) + a₃ φ(λ)²` (the `ν`-terms drop since `φ(ν) = 0`). -/
theorem finTwoEvalSndZero_formalGroupSub :
    finTwoEvalSndZero W.formalGroupSub
      = PowerSeries.C W.a₁ * finTwoEvalSndZero W.formalWDividedDiff
        + PowerSeries.C W.a₃ * finTwoEvalSndZero W.formalWDividedDiff ^ 2 := by
  simp only [formalGroupSub, map_add, map_mul, map_pow, map_ofNat, finTwoEvalSndZero_C,
    W.finTwoEvalSndZero_formalGroupNu, mul_zero, add_zero]

/-- **The quadratic root relation** `φ(A)·X² + φ(B)·X = φ(λ)`.  Apply `φ` to the collinearity cubic
`formalCubicResidual_root_zero`; substituting `w = φ(λ)·X` and `φ(ν) = 0` makes it `X·g = 0` with
`g = φ(A)·X² + φ(B)·X − φ(λ)`, and cancelling the non-zero-divisor `X` gives `g = 0`. -/
theorem finTwoEvalSndZero_quadratic :
    finTwoEvalSndZero W.formalGroupLead * PowerSeries.X ^ 2
      + finTwoEvalSndZero W.formalGroupSub * PowerSeries.X
      = finTwoEvalSndZero W.formalWDividedDiff := by
  have hres := congrArg finTwoEvalSndZero W.formalCubicResidual_root_zero
  simp only [map_add, map_sub, map_mul, map_pow, finTwoEvalSndZero_C, finTwoEvalSndZero_X_zero,
    map_zero, W.finTwoEvalSndZero_formalGroupNu, add_zero] at hres
  have hXg : PowerSeries.X
      * (finTwoEvalSndZero W.formalGroupLead * PowerSeries.X ^ 2
        + finTwoEvalSndZero W.formalGroupSub * PowerSeries.X
        - finTwoEvalSndZero W.formalWDividedDiff) = 0 := by
    rw [W.finTwoEvalSndZero_formalGroupLead, W.finTwoEvalSndZero_formalGroupSub]
    linear_combination hres
  have hg : finTwoEvalSndZero W.formalGroupLead * PowerSeries.X ^ 2
      + finTwoEvalSndZero W.formalGroupSub * PowerSeries.X
      - finTwoEvalSndZero W.formalWDividedDiff = 0 := by
    refine PowerSeries.ext fun n => ?_
    have hc := congrArg (PowerSeries.coeff (n + 1)) hXg
    rwa [PowerSeries.coeff_succ_X_mul, map_zero] at hc
  linear_combination hg

/-! ### Pushing `φ` through the inverses and the third-root/denominator data -/

/-- `φ(invOfUnit A 1) = Ring.inverse (φ A)` (`A = formalGroupLead`, constant coefficient `1`). -/
theorem finTwoEvalSndZero_invOfUnit_formalGroupLead :
    finTwoEvalSndZero (invOfUnit W.formalGroupLead 1)
      = Ring.inverse (finTwoEvalSndZero W.formalGroupLead) := by
  have hone : finTwoEvalSndZero W.formalGroupLead
      * finTwoEvalSndZero (invOfUnit W.formalGroupLead 1) = 1 := by
    rw [← map_mul, MvPowerSeries.mul_invOfUnit W.formalGroupLead 1
      (by rw [W.cc_formalGroupLead, Units.val_one]), map_one]
  have hu : IsUnit (finTwoEvalSndZero W.formalGroupLead) := IsUnit.of_mul_eq_one _ hone
  calc finTwoEvalSndZero (invOfUnit W.formalGroupLead 1)
      = Ring.inverse (finTwoEvalSndZero W.formalGroupLead)
          * finTwoEvalSndZero W.formalGroupLead
          * finTwoEvalSndZero (invOfUnit W.formalGroupLead 1) := by
        rw [Ring.inverse_mul_cancel _ hu, one_mul]
    _ = Ring.inverse (finTwoEvalSndZero W.formalGroupLead)
          * (finTwoEvalSndZero W.formalGroupLead
            * finTwoEvalSndZero (invOfUnit W.formalGroupLead 1)) := by rw [mul_assoc]
    _ = Ring.inverse (finTwoEvalSndZero W.formalGroupLead) := by rw [hone, mul_one]

/-- `φ(invOfUnit D 1) = Ring.inverse (φ D)` (`D = formalGroupDen`, constant coefficient `1`). -/
theorem finTwoEvalSndZero_invOfUnit_formalGroupDen :
    finTwoEvalSndZero (invOfUnit W.formalGroupDen 1)
      = Ring.inverse (finTwoEvalSndZero W.formalGroupDen) := by
  have hone : finTwoEvalSndZero W.formalGroupDen
      * finTwoEvalSndZero (invOfUnit W.formalGroupDen 1) = 1 := by
    rw [← map_mul, MvPowerSeries.mul_invOfUnit W.formalGroupDen 1
      (by rw [W.cc_formalGroupDen, Units.val_one]), map_one]
  have hu : IsUnit (finTwoEvalSndZero W.formalGroupDen) := IsUnit.of_mul_eq_one _ hone
  calc finTwoEvalSndZero (invOfUnit W.formalGroupDen 1)
      = Ring.inverse (finTwoEvalSndZero W.formalGroupDen)
          * finTwoEvalSndZero W.formalGroupDen
          * finTwoEvalSndZero (invOfUnit W.formalGroupDen 1) := by
        rw [Ring.inverse_mul_cancel _ hu, one_mul]
    _ = Ring.inverse (finTwoEvalSndZero W.formalGroupDen)
          * (finTwoEvalSndZero W.formalGroupDen
            * finTwoEvalSndZero (invOfUnit W.formalGroupDen 1)) := by rw [mul_assoc]
    _ = Ring.inverse (finTwoEvalSndZero W.formalGroupDen) := by rw [hone, mul_one]

/-- `φ(A)` is a unit of `R⟦z₁⟧`. -/
theorem isUnit_finTwoEvalSndZero_formalGroupLead :
    IsUnit (finTwoEvalSndZero W.formalGroupLead) := by
  have hone : finTwoEvalSndZero W.formalGroupLead
      * finTwoEvalSndZero (invOfUnit W.formalGroupLead 1) = 1 := by
    rw [← map_mul, MvPowerSeries.mul_invOfUnit W.formalGroupLead 1
      (by rw [W.cc_formalGroupLead, Units.val_one]), map_one]
  exact IsUnit.of_mul_eq_one _ hone

/-- `φ(D)` is a unit of `R⟦z₁⟧`. -/
theorem isUnit_finTwoEvalSndZero_formalGroupDen :
    IsUnit (finTwoEvalSndZero W.formalGroupDen) := by
  have hone : finTwoEvalSndZero W.formalGroupDen
      * finTwoEvalSndZero (invOfUnit W.formalGroupDen 1) = 1 := by
    rw [← map_mul, MvPowerSeries.mul_invOfUnit W.formalGroupDen 1
      (by rw [W.cc_formalGroupDen, Units.val_one]), map_one]
  exact IsUnit.of_mul_eq_one _ hone

/-- `φ(z₃') = −(φ(B)·Ring.inverse (φ A)) − X` (the `z₂ = X 1` term drops). -/
theorem finTwoEvalSndZero_formalThirdRoot :
    finTwoEvalSndZero W.formalThirdRoot
      = -(finTwoEvalSndZero W.formalGroupSub
          * Ring.inverse (finTwoEvalSndZero W.formalGroupLead)) - PowerSeries.X := by
  simp only [formalThirdRoot, map_sub, map_neg, map_mul,
    W.finTwoEvalSndZero_invOfUnit_formalGroupLead, finTwoEvalSndZero_X_zero,
    finTwoEvalSndZero_X_one, sub_zero]

/-- `φ(D) = 1 − a₁ φ(z₃') − a₃ (φ(λ)·φ(z₃'))` (the `ν`-term drops since `φ(ν) = 0`). -/
theorem finTwoEvalSndZero_formalGroupDen :
    finTwoEvalSndZero W.formalGroupDen
      = 1 - PowerSeries.C W.a₁ * finTwoEvalSndZero W.formalThirdRoot
        - PowerSeries.C W.a₃
          * (finTwoEvalSndZero W.formalWDividedDiff * finTwoEvalSndZero W.formalThirdRoot) := by
  simp only [formalGroupDen, map_sub, map_mul, map_add, map_one, finTwoEvalSndZero_C,
    W.finTwoEvalSndZero_formalGroupNu, add_zero]

/-! ### The base identity `F(z₁, 0) = z₁` -/

/-- **The base identity `F(z₁, 0) = z₁`** of the genuine `(z, w)` formal group law:
`finTwoEvalSndZero W.formalGroupZW = X`.  This is the group-law axiom `F(z, 0) = z` and discharges
the base hypothesis `hF` of `formalLog_subst_formalGroupZW_of_identity_star`. -/
theorem finTwoEvalSndZero_formalGroupZW :
    MvPowerSeries.finTwoEvalSndZero W.formalGroupZW = PowerSeries.X := by
  have hF : finTwoEvalSndZero W.formalGroupZW
      = -(finTwoEvalSndZero W.formalThirdRoot)
        * Ring.inverse (finTwoEvalSndZero W.formalGroupDen) := by
    rw [formalGroupZW, map_mul, map_neg, W.finTwoEvalSndZero_invOfUnit_formalGroupDen]
  -- The `μ`-cleared polynomial identity `B = X·(a₁ + a₃ λ)·(B + X·A)` from the root relation.
  have hpoly : finTwoEvalSndZero W.formalGroupSub
      = PowerSeries.X
        * (PowerSeries.C W.a₁ + PowerSeries.C W.a₃ * finTwoEvalSndZero W.formalWDividedDiff)
        * (finTwoEvalSndZero W.formalGroupSub
          + PowerSeries.X * finTwoEvalSndZero W.formalGroupLead) := by
    linear_combination W.finTwoEvalSndZero_formalGroupSub
      - (PowerSeries.C W.a₁ + PowerSeries.C W.a₃ * finTwoEvalSndZero W.formalWDividedDiff)
        * W.finTwoEvalSndZero_quadratic
  have hAiA : finTwoEvalSndZero W.formalGroupLead
      * Ring.inverse (finTwoEvalSndZero W.formalGroupLead) = 1 :=
    Ring.mul_inverse_cancel _ W.isUnit_finTwoEvalSndZero_formalGroupLead
  -- The key: `−φ(z₃') = X·φ(D)`, after clearing `Ring.inverse (φ A)` via `hpoly` and `hAiA`.
  have hkey : -(finTwoEvalSndZero W.formalThirdRoot)
      = PowerSeries.X * finTwoEvalSndZero W.formalGroupDen := by
    rw [W.finTwoEvalSndZero_formalGroupDen, W.finTwoEvalSndZero_formalThirdRoot]
    linear_combination Ring.inverse (finTwoEvalSndZero W.formalGroupLead) * hpoly
      + PowerSeries.X ^ 2
        * (PowerSeries.C W.a₁ + PowerSeries.C W.a₃ * finTwoEvalSndZero W.formalWDividedDiff) * hAiA
  rw [hF, hkey, mul_assoc,
    Ring.mul_inverse_cancel _ W.isUnit_finTwoEvalSndZero_formalGroupDen, mul_one]

/-- **Log-additivity of the formal logarithm, conditional only on the invariant-differential
invariance `(★)`.**  Combining the base identity `F(z₁, 0) = z₁`
(`finTwoEvalSndZero_formalGroupZW`) with `hstar` discharges both hypotheses of
`formalLog_subst_formalGroupZW_of_identity_star`, giving
`log_E(F) = log_E(z₁) + log_E(z₂)` (Silverman AEC IV.5, Proposition 5.2). -/
theorem formalLog_subst_formalGroupZW_of_star [Algebra ℚ R]
    (hstar : W.invariantDifferential.subst W.formalGroupZW * pderivSnd W.formalGroupZW
      = W.invariantDifferential.subst (X 1)) :
    W.formalLog.subst W.formalGroupZW = W.formalLog.subst (X 0) + W.formalLog.subst (X 1) :=
  W.formalLog_subst_formalGroupZW_of_identity_star W.finTwoEvalSndZero_formalGroupZW hstar

end WeierstrassCurve
