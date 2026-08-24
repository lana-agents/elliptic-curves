/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FormalGroup.Exponential
import EllipticCurves.FormalGroup.GroupLawBaseSlice

/-!
# Associativity of the genuine `(z, w)` formal group law via the `𝔾ₐ` isomorphism

This file proves **associativity** of the genuine bivariate Weierstrass formal group law
`W.formalGroupZW : MvPowerSeries (Fin 2) R` over a `ℚ`-algebra `R`, *conditional on the
log-additivity*

`hadd : log_E(F(z₁, z₂)) = log_E(z₁) + log_E(z₂)`
      i.e. `W.formalLog.subst W.formalGroupZW = W.formalLog.subst (X 0) + W.formalLog.subst (X 1)`

which is exactly the deliverable of issue #315 (the conclusion of
`WeierstrassCurve.formalLog_subst_formalGroupZW_of_star`).  This is **route 2** of Silverman
AEC IV.1/IV.5: over a `ℚ`-algebra the formal logarithm `log_E` is an isomorphism of formal groups
`F ≅ 𝔾ₐ` with inverse `exp_E = W.formalExp` (both merged, `Exponential.lean`, `#290`), and
associativity of `F` is a transport of the associativity of ordinary addition `+` on `𝔾ₐ`.

## Why this is independent of the identification `#310`/`#314`

This file takes `hadd` as a *hypothesis* and proves the **forward implication**
`log-additivity ⟹ associativity`,
which needs no identification and is not circular: it consumes `#315`'s output, it does not feed
`(★)`.  That independence is a property of the proof and is permanent.

⚠️ **Two clauses this section used to carry have gone false, for two unrelated reasons, and both
are recorded rather than deleted.**

* It read *"The invariant-differential invariance `(★)` that discharges `hadd` unconditionally is
  gated on the Laurent identification `#310`"*.  ⚠️ **That named the wrong gate**, and it would
  have named the wrong gate even had `#310` still been open: `(★)` is closed on the Laurent side
  from `hWF` (#333, `GenuineWThreeIdentification.lean`) and `hdiff` (#338,
  `VietaDifferential.lean`), by the route `InvariantDifferentialInvariance.lean` sets out — not
  through the identification at all.  ⚠️ Separately, `#310` **has** landed
  (`embedDoubleLaurent_formalGroupZW`, `GenuineLawTransfer.lean`).  *A gate clause can be false
  because the gate was paid and false because it was never the gate; repairing only the date leaves
  the dependency wrong.*
* It read *"The instant `#315` lands the unconditional `hadd`, the unconditional associativity …
  drops out"*.  It has landed, and it did drop out:
  `WeierstrassCurve.formalGroupZW_assoc_unconditional`
  (`EllipticCurves.FormalGroup.GroupLawAssocUnconditional`, `#319`) is this file's
  `formalGroupZW_assoc` with `WeierstrassCurve.formalLog_subst_formalGroupZW`
  (`EllipticCurves.FormalGroup.LogAdditivityUnconditional`, `#315`) fed in.  ⚠️ **And the `#263`
  bundle went further than the promise**: `WeierstrassCurve.formalGroup : FormalGroup R` in
  `EllipticCurves.FormalGroup.GroupLawBundleGeneral` is unconditional over an **arbitrary**
  `CommRing R`, not merely over a `ℚ`-algebra, by the universality transfer.

## Main results (all sorry-free)

* `WeierstrassCurve.formalExp_subst_formalLog_subst` :
  `exp_E(log_E(g)) = g` for any substitutable `g : MvPowerSeries τ R` — the `𝔾ₐ`-iso inverse,
  transported along an arbitrary substitution.
* `WeierstrassCurve.formalLog_subst_formalGroupZW_subst` :
  `log_E(F(g₀, g₁)) = log_E(g₀) + log_E(g₁)` — `hadd` pushed forward along a substitution
  `g : Fin 2 → MvPowerSeries τ R`.
* `WeierstrassCurve.formalGroupZW_assoc_of_logAdditivity` :
  the general (`FormalGroup.assoc'`-shaped) associativity over arbitrary substitutands.
* `WeierstrassCurve.formalGroupZW_assoc` :
  the exact `FormalGroup.assoc`-field shape `F(F(X₀, X₁), X₂) = F(X₀, F(X₁, X₂))` in
  `MvPowerSeries (Fin 3) R`, which `#263` plugs straight into the `FormalGroup R` constructor.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1; IV.5,
  Propositions 5.2, 5.5.
-/

open MvPowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- **Naturality of `PowerSeries` substitution under an `MvPowerSeries` substitution.**
For a univariate `p : R⟦X⟧`, a bivariate `G` and a substitution `g : Fin 2 → MvPowerSeries τ R`,
substituting `g` into `p.subst G` is the same as substituting `g` into `G` first:
`(p ∘ G) ∘ g = p ∘ (G ∘ g)`.  This is the algebraic engine that pushes the log-additivity
`hadd` forward along a substitution. -/
private theorem subst_powerSeries_natural {τ : Type*} (p : PowerSeries R)
    {G : MvPowerSeries (Fin 2) R} (hG : PowerSeries.HasSubst G)
    {g : Fin 2 → MvPowerSeries τ R} (hg : MvPowerSeries.HasSubst g) :
    MvPowerSeries.subst g (p.subst G) = p.subst (MvPowerSeries.subst g G) := by
  have hconst : MvPowerSeries.HasSubst (fun _ : Unit => G) :=
    MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun _ => hG)
  rw [PowerSeries.subst_def, PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply hconst hg]

/-- **`exp_E ∘ log_E = id`, transported along a substitution.**
`exp_E(log_E(g)) = g` for any substitutable `g : MvPowerSeries τ R`.  This is the inverse half of
the `𝔾ₐ` isomorphism `log_E : F ≅ 𝔾ₐ`; it says `log_E` is injective on substitutable series. -/
theorem formalExp_subst_formalLog_subst [Algebra ℚ R] {τ : Type*} {g : MvPowerSeries τ R}
    (hg : PowerSeries.HasSubst g) :
    W.formalExp.subst (W.formalLog.subst g) = g := by
  have hL : PowerSeries.HasSubst W.formalLog :=
    PowerSeries.HasSubst.of_constantCoeff_zero' W.constantCoeff_formalLog
  rw [← PowerSeries.subst_comp_subst_apply hL hg, W.formalExp_subst_formalLog,
    PowerSeries.subst_X hg]

/-- **Log-additivity pushed forward along a substitution.**
Given the log-additivity `hadd` on `F = W.formalGroupZW`, for any substitution
`g : Fin 2 → MvPowerSeries τ R`,
`log_E(F(g₀, g₁)) = log_E(g₀) + log_E(g₁)`. -/
theorem formalLog_subst_formalGroupZW_subst [Algebra ℚ R]
    (hadd : W.formalLog.subst W.formalGroupZW
      = W.formalLog.subst (X 0) + W.formalLog.subst (X 1))
    {τ : Type*} {g : Fin 2 → MvPowerSeries τ R} (hg : MvPowerSeries.HasSubst g) :
    W.formalLog.subst (W.formalGroupZW.subst g)
      = W.formalLog.subst (g 0) + W.formalLog.subst (g 1) := by
  have h := congrArg (MvPowerSeries.substAlgHom hg) hadd
  rw [map_add] at h
  simp only [MvPowerSeries.coe_substAlgHom hg] at h
  rw [subst_powerSeries_natural W.formalLog W.hasSubst_formalGroupZW hg,
    subst_powerSeries_natural W.formalLog (PowerSeries.HasSubst.X 0) hg,
    subst_powerSeries_natural W.formalLog (PowerSeries.HasSubst.X 1) hg,
    MvPowerSeries.subst_X hg 0, MvPowerSeries.subst_X hg 1] at h
  exact h

/-- Substituting a family of substitutable series into a `Fin 2`-vector `![a, b]` is
substitutable. -/
private theorem hasSubst_pair {τ : Type*} {a b : MvPowerSeries τ R}
    (ha : PowerSeries.HasSubst a) (hb : PowerSeries.HasSubst b) :
    MvPowerSeries.HasSubst (![a, b] : Fin 2 → MvPowerSeries τ R) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_nilpotent ?_
  intro s; fin_cases s
  · simpa using ha
  · simpa using hb

/-- **Associativity of the genuine `(z, w)` formal group law over a `ℚ`-algebra, conditional on
log-additivity `hadd` (issue #315).**  The general `FormalGroup.assoc'`-shaped statement over
arbitrary substitutands `f₀, f₁, f₂`.

The proof is the `𝔾ₐ` transport: applying `log_E` to both sides and splitting twice via
`formalLog_subst_formalGroupZW_subst` collapses each side to
`log_E(f₀) + log_E(f₁) + log_E(f₂)` (matching by `add_assoc`); then `exp_E ∘ log_E = id`
(`formalExp_subst_formalLog_subst`) cancels the logarithm. -/
theorem formalGroupZW_assoc_of_logAdditivity [Algebra ℚ R]
    (hadd : W.formalLog.subst W.formalGroupZW
      = W.formalLog.subst (X 0) + W.formalLog.subst (X 1))
    {τ : Type*} {f₀ f₁ f₂ : MvPowerSeries τ R}
    (h₀ : PowerSeries.HasSubst f₀) (h₁ : PowerSeries.HasSubst f₁) (h₂ : PowerSeries.HasSubst f₂) :
    W.formalGroupZW.subst ![W.formalGroupZW.subst ![f₀, f₁], f₂]
      = W.formalGroupZW.subst ![f₀, W.formalGroupZW.subst ![f₁, f₂]] := by
  have hF : MvPowerSeries.constantCoeff W.formalGroupZW = 0 := W.constantCoeff_formalGroupZW
  have hnil : IsNilpotent (MvPowerSeries.constantCoeff W.formalGroupZW) := by
    rw [hF]; exact IsNilpotent.zero
  have hg01 := hasSubst_pair h₀ h₁
  have hg12 := hasSubst_pair h₁ h₂
  have hinnerL : PowerSeries.HasSubst (W.formalGroupZW.subst ![f₀, f₁]) :=
    MvPowerSeries.IsNilpotent_subst hg01 hnil
  have hinnerR : PowerSeries.HasSubst (W.formalGroupZW.subst ![f₁, f₂]) :=
    MvPowerSeries.IsNilpotent_subst hg12 hnil
  have hAL : PowerSeries.HasSubst
      (W.formalGroupZW.subst ![W.formalGroupZW.subst ![f₀, f₁], f₂]) :=
    MvPowerSeries.IsNilpotent_subst (hasSubst_pair hinnerL h₂) hnil
  have hAR : PowerSeries.HasSubst
      (W.formalGroupZW.subst ![f₀, W.formalGroupZW.subst ![f₁, f₂]]) :=
    MvPowerSeries.IsNilpotent_subst (hasSubst_pair h₀ hinnerR) hnil
  -- `log_E` of the left side collapses to `(L f₀ + L f₁) + L f₂`.
  have hlogL : W.formalLog.subst (W.formalGroupZW.subst ![W.formalGroupZW.subst ![f₀, f₁], f₂])
      = W.formalLog.subst f₀ + W.formalLog.subst f₁ + W.formalLog.subst f₂ := by
    rw [W.formalLog_subst_formalGroupZW_subst hadd (hasSubst_pair hinnerL h₂)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [W.formalLog_subst_formalGroupZW_subst hadd hg01]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  -- `log_E` of the right side collapses to `L f₀ + (L f₁ + L f₂)`.
  have hlogR : W.formalLog.subst (W.formalGroupZW.subst ![f₀, W.formalGroupZW.subst ![f₁, f₂]])
      = W.formalLog.subst f₀ + (W.formalLog.subst f₁ + W.formalLog.subst f₂) := by
    rw [W.formalLog_subst_formalGroupZW_subst hadd (hasSubst_pair h₀ hinnerR)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [W.formalLog_subst_formalGroupZW_subst hadd hg12]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hlog : W.formalLog.subst (W.formalGroupZW.subst ![W.formalGroupZW.subst ![f₀, f₁], f₂])
      = W.formalLog.subst (W.formalGroupZW.subst ![f₀, W.formalGroupZW.subst ![f₁, f₂]]) := by
    rw [hlogL, hlogR, add_assoc]
  calc W.formalGroupZW.subst ![W.formalGroupZW.subst ![f₀, f₁], f₂]
      = W.formalExp.subst (W.formalLog.subst
          (W.formalGroupZW.subst ![W.formalGroupZW.subst ![f₀, f₁], f₂])) :=
        (W.formalExp_subst_formalLog_subst hAL).symm
    _ = W.formalExp.subst (W.formalLog.subst
          (W.formalGroupZW.subst ![f₀, W.formalGroupZW.subst ![f₁, f₂]])) := by rw [hlog]
    _ = W.formalGroupZW.subst ![f₀, W.formalGroupZW.subst ![f₁, f₂]] :=
        W.formalExp_subst_formalLog_subst hAR

/-- **Associativity of `W.formalGroupZW`, in the exact `FormalGroup.assoc`-field shape**
`F(F(X₀, X₁), X₂) = F(X₀, F(X₁, X₂))` in `MvPowerSeries (Fin 3) R`, conditional on log-additivity
`hadd` (issue #315).  This is the identity `#263` feeds to the `FormalGroup R` `assoc` field. -/
theorem formalGroupZW_assoc [Algebra ℚ R]
    (hadd : W.formalLog.subst W.formalGroupZW
      = W.formalLog.subst (X 0) + W.formalLog.subst (X 1)) :
    W.formalGroupZW.subst
        ![W.formalGroupZW.subst ![(X 0 : MvPowerSeries (Fin 3) R), X 1], X 2]
      = W.formalGroupZW.subst
        ![(X 0 : MvPowerSeries (Fin 3) R), W.formalGroupZW.subst ![X 1, X 2]] :=
  W.formalGroupZW_assoc_of_logAdditivity hadd (PowerSeries.HasSubst.X 0)
    (PowerSeries.HasSubst.X 1) (PowerSeries.HasSubst.X 2)

end WeierstrassCurve
