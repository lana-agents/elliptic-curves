/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FormalGroup.LogAdditivityStar
import EllipticCurves.FormalGroup.GroupLawBaseSlice
import EllipticCurves.FormalGroup.EmbedDictionary
import EllipticCurves.FormalGroup.FormalGroupLaurent
import EllipticCurves.FormalGroup.Logarithm

/-!
# Closing the invariant-differential invariance `(★)` of issue #315

This file assembles the invariant-differential invariance
`(★)  (ω_E ∘ F)·∂_{z₂}F = ω_E(z₂)`   (`hstar`)
of the genuine `(z, w)` formal group law `F = W.formalGroupZW`, and feeds it into the merged
consumer `WeierstrassCurve.formalLog_subst_formalGroupZW_of_star` to obtain the **log-additivity of
the formal logarithm** (Silverman AEC IV.5, Proposition 5.2):
`log_E(F(z₁, z₂)) = log_E(z₁) + log_E(z₂)`.

## Strategy (Route B, via the double-Laurent writer `edl = HahnSeries.embedDoubleLaurent`)

Writing `F = W.formalGroupZW`, `WF = W.formalW.subst F` (order-3), `ωF = ω_E ∘ F`,
`ω₂ = ω_E(z₂) = W.invariantDifferential.subst (X 1)`, `∂₂ = MvPowerSeries.pderivSnd`,
`cofF = -2 + a₁·F + a₃·WF`, the reduction proceeds through the *polynomial frontier*

`POLY-★ :  WF·∂₂F − F·∂₂WF = ω₂·(WF·cofF)`

and the *explicit Laurent differential identity*

`hdiff :  x₃' = ω̃₂·(2·y₃ + a₁·x₃ + a₃)`   (`ω̃₂ = (ω_E : R⸨X⸩).map HahnSeries.C`)

as follows.

* **Stage A** computes `edl ω₂ = ω̃₂` (the writer image of the outer invariant differential).
* **Stage B** (`hstar_of_polystar`) derives `hstar` from `POLY-★`: combining `Eq.A`
  (`invariantDifferential_mul_clear_subst_mul_pderivSnd`) with `POLY-★` gives
  `(ωF·∂₂F − ω₂)·(WF·cofF) = 0`; the cofactor `cofF` is a unit (constant term `−2`), so it cancels,
  and after applying `edl` the order-3 factor `WF` becomes the *unit* `W₃ = edl WF` (via `hWF`,
  issue #333), leaving `ωF·∂₂F − ω₂ = 0` by injectivity of `edl`.
* **Stage C** (`polystar_of_hdiff`) derives `POLY-★` from `hdiff` by pushing `edl` through
  `POLY-★` (Leibniz calculus `embedDoubleLaurent_pderivSnd`, the addition-law identities
  `formalWThree_mul_derivative_formalGroupLaurent_sub` and `formalWThree_mul_cofactor`), reducing to
  `hdiff` scaled by the unit `y₃⁻²`, then re-applying injectivity.

`hWF : edl WF = W₃` is issue #333's deliverable and is carried as an explicit hypothesis.
`hdiff` is the Silverman IV.5.2 translation invariance in explicit Laurent coordinates; when it is
supplied the log-additivity conclusion follows unconditionally-but-for-`hWF`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4, Theorem 4.2; IV.5,
  Proposition 5.2.
-/

open MvPowerSeries
open scoped LaurentSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### Stage A — the writer image of the outer invariant differential -/

/-- **Stage A.**  The writer image of the outer invariant differential `ω_E(z₂)` is
`ω̃₂ = (ω_E : R⸨X⸩).map HahnSeries.C`.  Combines `PowerSeries.toMvPowerSeries_eq_subst` (the
single-variable substitution `ω_E(X 1)` is the `z₂`-axis embedding) with
`HahnSeries.embedDoubleLaurent_toMvPowerSeries_one`. -/
theorem embedDoubleLaurent_invariantDifferential_subst_X_one [Algebra ℚ R] :
    HahnSeries.embedDoubleLaurent (W.invariantDifferential.subst (X 1))
      = (W.invariantDifferential : R⸨X⸩).map (HahnSeries.C : R →+* R⸨X⸩) := by
  rw [← PowerSeries.toMvPowerSeries_eq_subst,
    HahnSeries.embedDoubleLaurent_toMvPowerSeries_one]

/-! ### Stage B — `hstar` from the polynomial frontier `POLY-★` -/

/-- **Stage B.**  The invariant-differential invariance `(★)` (`hstar`) follows from the polynomial
frontier `POLY-★` together with `hWF : edl WF = W₃`.  See the module docstring for the argument. -/
theorem hstar_of_polystar [Algebra ℚ R]
    (hWF : HahnSeries.embedDoubleLaurent (W.formalW.subst W.formalGroupZW) = W.formalWThree)
    (hps : W.formalW.subst W.formalGroupZW * MvPowerSeries.pderivSnd W.formalGroupZW
          - W.formalGroupZW * MvPowerSeries.pderivSnd (W.formalW.subst W.formalGroupZW)
        = W.invariantDifferential.subst (X 1)
          * (W.formalW.subst W.formalGroupZW
            * (-2 + MvPowerSeries.C W.a₁ * W.formalGroupZW
              + MvPowerSeries.C W.a₃ * W.formalW.subst W.formalGroupZW))) :
    W.invariantDifferential.subst W.formalGroupZW * MvPowerSeries.pderivSnd W.formalGroupZW
      = W.invariantDifferential.subst (X 1) := by
  -- `Eq.A`: `ωF·∂₂F·(WF·cofF) = WF·∂₂F − F·∂₂WF`.
  have hA := W.invariantDifferential_mul_clear_subst_mul_pderivSnd
  -- Combine with `POLY-★`: `(ωF·∂₂F − ω₂)·(WF·cofF) = 0`.
  have hzero : (W.invariantDifferential.subst W.formalGroupZW
        * MvPowerSeries.pderivSnd W.formalGroupZW - W.invariantDifferential.subst (X 1))
      * (W.formalW.subst W.formalGroupZW
        * (-2 + MvPowerSeries.C W.a₁ * W.formalGroupZW
          + MvPowerSeries.C W.a₃ * W.formalW.subst W.formalGroupZW)) = 0 := by
    linear_combination hA + hps
  -- `cofF` is a unit: its constant coefficient is `−2`, a unit in the `ℚ`-algebra `R`.
  have hWFcc : MvPowerSeries.constantCoeff (W.formalW.subst W.formalGroupZW) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero W.constantCoeff_formalGroupZW W.formalW
      W.constantCoeff_formalW
  have hcof : IsUnit (-2 + MvPowerSeries.C W.a₁ * W.formalGroupZW
      + MvPowerSeries.C W.a₃ * W.formalW.subst W.formalGroupZW) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    have hcc : MvPowerSeries.constantCoeff (-2 + MvPowerSeries.C W.a₁ * W.formalGroupZW
        + MvPowerSeries.C W.a₃ * W.formalW.subst W.formalGroupZW) = -2 := by
      rw [map_add, map_add, map_neg, map_ofNat, map_mul, map_mul, MvPowerSeries.constantCoeff_C,
        MvPowerSeries.constantCoeff_C, W.constantCoeff_formalGroupZW, hWFcc]
      ring
    rw [hcc]
    exact ⟨negTwoUnit R, negTwoUnit_val R⟩
  -- Cancel `cofF`: `(ωF·∂₂F − ω₂)·WF = 0`.
  have hWFmul : (W.invariantDifferential.subst W.formalGroupZW
        * MvPowerSeries.pderivSnd W.formalGroupZW - W.invariantDifferential.subst (X 1))
      * W.formalW.subst W.formalGroupZW = 0 := by
    have := (IsUnit.mul_left_eq_zero hcof).mp (by rw [← mul_assoc] at hzero; exact hzero)
    exact this
  -- Apply the writer ring hom and use `hWF` to expose the *unit* `W₃`.
  have himg := congrArg HahnSeries.embedDoubleLaurentRingHom hWFmul
  rw [map_mul, map_zero, HahnSeries.embedDoubleLaurentRingHom_apply,
    HahnSeries.embedDoubleLaurentRingHom_apply, hWF] at himg
  -- `W₃` is a unit, so the first factor vanishes.
  have hW3unit : IsUnit W.formalWThree := by
    rw [formalWThree]
    exact (W.isUnit_formalYThree.ringInverse).neg
  have hedl0 : HahnSeries.embedDoubleLaurent
      (W.invariantDifferential.subst W.formalGroupZW
        * MvPowerSeries.pderivSnd W.formalGroupZW - W.invariantDifferential.subst (X 1)) = 0 :=
    (IsUnit.mul_left_eq_zero hW3unit).mp himg
  -- Injectivity of the writer gives `ωF·∂₂F − ω₂ = 0`.
  rw [← sub_eq_zero]
  exact HahnSeries.embedDoubleLaurent_injective
    (by rw [hedl0, ← HahnSeries.embedDoubleLaurentRingHom_apply, map_zero])

/-! ### Stage C — the polynomial frontier `POLY-★` from the Laurent identity `hdiff` -/

/-- **Stage C.**  The polynomial frontier `POLY-★` follows from the explicit Laurent differential
identity `hdiff : x₃' = ω̃₂·(2·y₃ + a₁·x₃ + a₃)` together with `hWF : edl WF = W₃`.  The proof
applies the injective writer `edl` to both sides of `POLY-★` and reduces via the Leibniz calculus
and the addition-law identities to `hdiff` scaled by the unit `y₃⁻²`. -/
theorem polystar_of_hdiff [Algebra ℚ R]
    (hWF : HahnSeries.embedDoubleLaurent (W.formalW.subst W.formalGroupZW) = W.formalWThree)
    (hd : LaurentSeries.derivative ℤ W.formalXThree
      = (W.invariantDifferential : R⸨X⸩).map (HahnSeries.C : R →+* R⸨X⸩)
        * (2 * W.formalYThree + HahnSeries.C (HahnSeries.C W.a₁) * W.formalXThree
          + HahnSeries.C (HahnSeries.C W.a₃))) :
    W.formalW.subst W.formalGroupZW * MvPowerSeries.pderivSnd W.formalGroupZW
        - W.formalGroupZW * MvPowerSeries.pderivSnd (W.formalW.subst W.formalGroupZW)
      = W.invariantDifferential.subst (X 1)
        * (W.formalW.subst W.formalGroupZW
          * (-2 + MvPowerSeries.C W.a₁ * W.formalGroupZW
            + MvPowerSeries.C W.a₃ * W.formalW.subst W.formalGroupZW)) := by
  apply HahnSeries.embedDoubleLaurent_injective
  -- Writer image of the numerator `WF·∂₂F − F·∂₂WF`.
  have e1 : HahnSeries.embedDoubleLaurent
        (W.formalW.subst W.formalGroupZW * MvPowerSeries.pderivSnd W.formalGroupZW
          - W.formalGroupZW * MvPowerSeries.pderivSnd (W.formalW.subst W.formalGroupZW))
      = (Ring.inverse W.formalYThree) ^ 2 * LaurentSeries.derivative ℤ W.formalXThree := by
    rw [← HahnSeries.embedDoubleLaurentRingHom_apply]
    simp only [map_sub, map_mul, HahnSeries.embedDoubleLaurentRingHom_apply,
      HahnSeries.embedDoubleLaurent_pderivSnd, W.embedDoubleLaurent_formalGroupZW, hWF]
    exact W.formalWThree_mul_derivative_formalGroupLaurent_sub
  -- Writer image of `ω₂·(WF·cofF)`.
  have e2 : HahnSeries.embedDoubleLaurent
        (W.invariantDifferential.subst (X 1)
          * (W.formalW.subst W.formalGroupZW
            * (-2 + MvPowerSeries.C W.a₁ * W.formalGroupZW
              + MvPowerSeries.C W.a₃ * W.formalW.subst W.formalGroupZW)))
      = (W.invariantDifferential : R⸨X⸩).map (HahnSeries.C : R →+* R⸨X⸩)
        * ((Ring.inverse W.formalYThree) ^ 2
          * (2 * W.formalYThree + HahnSeries.C (HahnSeries.C W.a₁) * W.formalXThree
            + HahnSeries.C (HahnSeries.C W.a₃))) := by
    rw [← HahnSeries.embedDoubleLaurentRingHom_apply]
    simp only [map_mul, map_add, map_neg, map_ofNat, HahnSeries.embedDoubleLaurentRingHom_apply,
      HahnSeries.embedDoubleLaurent_C, W.embedDoubleLaurent_formalGroupZW, hWF,
      W.embedDoubleLaurent_invariantDifferential_subst_X_one]
    rw [W.formalWThree_mul_cofactor]
  rw [e1, e2]
  linear_combination (Ring.inverse W.formalYThree) ^ 2 * hd

/-! ### Assembly -/

/-- **`hstar` from the Laurent identity `hdiff`.**  Composition of Stages C and B. -/
theorem hstar_of_hdiff [Algebra ℚ R]
    (hWF : HahnSeries.embedDoubleLaurent (W.formalW.subst W.formalGroupZW) = W.formalWThree)
    (hd : LaurentSeries.derivative ℤ W.formalXThree
      = (W.invariantDifferential : R⸨X⸩).map (HahnSeries.C : R →+* R⸨X⸩)
        * (2 * W.formalYThree + HahnSeries.C (HahnSeries.C W.a₁) * W.formalXThree
          + HahnSeries.C (HahnSeries.C W.a₃))) :
    W.invariantDifferential.subst W.formalGroupZW * MvPowerSeries.pderivSnd W.formalGroupZW
      = W.invariantDifferential.subst (X 1) :=
  W.hstar_of_polystar hWF (W.polystar_of_hdiff hWF hd)

/-- **Log-additivity of the formal logarithm, conditional on `hWF` (issue #333) and the Laurent
differential identity `hdiff`.**  Feeding `hstar_of_hdiff` into the merged consumer
`formalLog_subst_formalGroupZW_of_star` gives
`log_E(F(z₁, z₂)) = log_E(z₁) + log_E(z₂)` (Silverman AEC IV.5, Proposition 5.2). -/
theorem formalLog_subst_formalGroupZW_of_hWF_hdiff [Algebra ℚ R]
    (hWF : HahnSeries.embedDoubleLaurent (W.formalW.subst W.formalGroupZW) = W.formalWThree)
    (hd : LaurentSeries.derivative ℤ W.formalXThree
      = (W.invariantDifferential : R⸨X⸩).map (HahnSeries.C : R →+* R⸨X⸩)
        * (2 * W.formalYThree + HahnSeries.C (HahnSeries.C W.a₁) * W.formalXThree
          + HahnSeries.C (HahnSeries.C W.a₃))) :
    W.formalLog.subst W.formalGroupZW = W.formalLog.subst (X 0) + W.formalLog.subst (X 1) :=
  W.formalLog_subst_formalGroupZW_of_star (W.hstar_of_hdiff hWF hd)

end WeierstrassCurve
