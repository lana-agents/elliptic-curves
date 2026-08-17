/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FormalGroup.GroupLawAssoc
import EllipticCurves.FormalGroup.LogAdditivityUnconditional

/-!
# The formal exponential is a homomorphism `𝔾ₐ → F_E` (issue #517)

Over a `ℚ`-algebra `R`, the formal logarithm `log_E = W.formalLog` and its compositional inverse the
formal exponential `exp_E = W.formalExp` (`Exponential.lean`) together exhibit the additive
isomorphism `Ê(𝔪) ≅ 𝔾ₐ` of Silverman AEC IV.5–IV.6.  The `log_E`-side of that isomorphism is
**log-additivity**, now merged unconditionally as
`WeierstrassCurve.formalLog_subst_formalGroupZW` (`LogAdditivityUnconditional.lean`, #315):

`log_E(F(z₁, z₂)) = log_E(z₁) + log_E(z₂)`.

This file supplies the dual `exp_E`-side — the **bivariate homomorphism half** — that `exp_E`
intertwines ordinary addition `+` on `𝔾ₐ` with the genuine `(z, w)` formal group law
`F = W.formalGroupZW`:

* `WeierstrassCurve.formalExp_subst_add_eq_formalGroupZW_subst` :
  `exp_E(z₁ + z₂) = F(exp_E z₁, exp_E z₂)`,
  i.e. `W.formalExp.subst (X 0 + X 1) = W.formalGroupZW.subst ![exp_E z₁, exp_E z₂]`
  in `MvPowerSeries (Fin 2) R`.

Together with the univariate inverse facts `formalLog_subst_formalExp` / `formalExp_subst_formalLog`
(`Exponential.lean`) this completes the `Ê(𝔪) ≅ 𝔾ₐ` isomorphism claim as a formal-group
*homomorphism* in both directions.

## Strategy

The proof is the `𝔾ₐ`-transport dual to the associativity proof in `GroupLawAssoc.lean`.  Set
`e_i := exp_E(X i)`.  Applying `log_E` to `F(e₀, e₁)` and splitting via the pushed-forward
log-additivity `formalLog_subst_formalGroupZW_subst` collapses it to
`log_E(e₀) + log_E(e₁) = X 0 + X 1` (using `log_E(exp_E(X i)) = X i`, a substitution transport of
`formalLog_subst_formalExp`).  Then `exp_E ∘ log_E = id` (`formalExp_subst_formalLog_subst`) cancels
the logarithm: `exp_E(X 0 + X 1) = exp_E(log_E(F(e₀, e₁))) = F(e₀, e₁)`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.5–IV.6 (the formal
  logarithm/exponential and the isomorphism `Ê(𝔪) ≅ 𝔾ₐ`).
-/

open MvPowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- **`log_E(exp_E(g)) = g` for a substitutable `g`.**  A substitution transport of the univariate
inverse `formalLog_subst_formalExp` (`log_E ∘ exp_E = id`): the `𝔾ₐ`-iso forward half. -/
theorem formalLog_subst_formalExp_subst [Algebra ℚ R] {τ : Type*} {g : MvPowerSeries τ R}
    (hg : PowerSeries.HasSubst g) :
    W.formalLog.subst (W.formalExp.subst g) = g := by
  have hExp : PowerSeries.HasSubst W.formalExp :=
    PowerSeries.HasSubst.of_constantCoeff_zero' W.constantCoeff_formalExp
  rw [← PowerSeries.subst_comp_subst_apply hExp hg, W.formalLog_subst_formalExp,
    PowerSeries.subst_X hg]

/-- **The formal exponential is a homomorphism `𝔾ₐ → F_E` (Silverman AEC IV.5–IV.6, bivariate half
of `Ê(𝔪) ≅ 𝔾ₐ`).**  Over a `ℚ`-algebra, `exp_E` intertwines ordinary addition with the genuine
`(z, w)` formal group law `F = W.formalGroupZW`:
`exp_E(z₁ + z₂) = F(exp_E z₁, exp_E z₂)`   in `MvPowerSeries (Fin 2) R`. -/
theorem formalExp_subst_add_eq_formalGroupZW_subst [Algebra ℚ R] :
    W.formalExp.subst ((X 0 : MvPowerSeries (Fin 2) R) + X 1)
      = W.formalGroupZW.subst
          ![W.formalExp.subst (X 0), W.formalExp.subst (X 1)] := by
  -- `HasSubst` facts for the substituted exponentials `e_i = exp_E(X i)`.
  have he0 : PowerSeries.HasSubst (W.formalExp.subst (X 0 : MvPowerSeries (Fin 2) R)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero
      (PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X 0) W.formalExp
        W.constantCoeff_formalExp)
  have he1 : PowerSeries.HasSubst (W.formalExp.subst (X 1 : MvPowerSeries (Fin 2) R)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero
      (PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X 1) W.formalExp
        W.constantCoeff_formalExp)
  have hpair : MvPowerSeries.HasSubst
      (![W.formalExp.subst (X 0), W.formalExp.subst (X 1)] : Fin 2 → MvPowerSeries (Fin 2) R) := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_nilpotent ?_
    intro s; fin_cases s
    · simpa using he0
    · simpa using he1
  have hnil : IsNilpotent (MvPowerSeries.constantCoeff W.formalGroupZW) := by
    rw [W.constantCoeff_formalGroupZW]; exact IsNilpotent.zero
  have hRHS := MvPowerSeries.IsNilpotent_subst hpair hnil
  have hX0 : PowerSeries.HasSubst (X 0 : MvPowerSeries (Fin 2) R) := PowerSeries.HasSubst.X 0
  have hX1 : PowerSeries.HasSubst (X 1 : MvPowerSeries (Fin 2) R) := PowerSeries.HasSubst.X 1
  -- `log_E` of `F(e₀, e₁)` collapses to `X 0 + X 1`.
  have key : W.formalLog.subst
      (W.formalGroupZW.subst ![W.formalExp.subst (X 0), W.formalExp.subst (X 1)])
      = (X 0 : MvPowerSeries (Fin 2) R) + X 1 := by
    rw [W.formalLog_subst_formalGroupZW_subst W.formalLog_subst_formalGroupZW hpair]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [W.formalLog_subst_formalExp_subst hX0, W.formalLog_subst_formalExp_subst hX1]
  -- Cancel the logarithm via `exp_E ∘ log_E = id`.
  rw [← key, W.formalExp_subst_formalLog_subst hRHS]

end WeierstrassCurve
