/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FormalGroup.GroupLawAssoc
import EllipticCurves.FormalGroup.LogMulByN

/-!
# The `ℤ`-action on the exp side: `exp_E ∘ i = i ∘ exp_E` and `exp_E(n·z) = [n](exp_E z)`

Over a `ℚ`-algebra `R`, the formal exponential `exp_E = W.formalExp` (`Exponential.lean`) is the
compositional inverse of the formal logarithm `log_E = W.formalLog`, exhibiting the additive
isomorphism `Ê(𝔪) ≅ 𝔾ₐ` (Silverman AEC IV.5–IV.6).  This file records the `exp_E`-side of the
`ℤ`-equivariance of that isomorphism — the exact dual of the merged log-side ℤ-action
(`LogMulByN.lean`, #519): `exp_E` carries multiplication-by-`n` on the additive group `𝔾ₐ` to the
formal-group `ℤ`-action `[n] = W.formalGroup.mulByN` / `mulByZ`, and negation to the formal inverse
`i = W.formalGroup.formalInv`.

* `WeierstrassCurve.formalExp_subst_nsmul_X` : `exp_E(n·z) = [n](exp_E z)` for `n : ℕ`;
* `WeierstrassCurve.formalExp_subst_neg_X` : `exp_E(-z) = i(exp_E z)`;
* `WeierstrassCurve.formalExp_subst_zsmul_X` : `exp_E(n·z) = [n](exp_E z)` for every `n : ℤ`.

Together with the log side (#519), the bivariate exp-homomorphism (#517), log-additivity and the
mutual-inverse laws, this closes the `ℤ`-equivariance of the `Ê(𝔪) ≅ 𝔾ₐ` picture on both sides.

## Strategy

Every statement transports a log-side identity through `exp_E ∘ log_E = id`.  For a series
`β : PowerSeries R` with zero constant coefficient, `formalExp_endo_transport` records
`β ∘ exp_E = exp_E ∘ (log_E ∘ β ∘ exp_E)` (the substitution-composition
`PowerSeries.subst_comp_subst_apply` followed by `formalExp_subst_formalLog_subst`).  Taking
`β = [n]` / `i` / `[n]_ℤ` and rewriting the inner `log_E ∘ β` by the log-side ℤ-action leaves
`(n • log_E) ∘ exp_E` (resp. `(-log_E) ∘ exp_E`); pushing the scalar through the substitution
`AlgHom` and applying `log_E ∘ exp_E = X` finishes.

## References

Silverman, *The Arithmetic of Elliptic Curves*, IV.6.
-/

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R)

/-- **Transporting a formal-group endomorphism through `exp_E ∘ log_E = id`.**  For a series
`β : PowerSeries R` with zero constant coefficient (so `β ∘ exp_E` is again substitutable),
`β(exp_E(z)) = exp_E(log_E(β(exp_E(z))))`.  Rewriting the inner `log_E ∘ β` by the log-side
ℤ-action turns this into the `exp_E`-side ℤ-action. -/
theorem formalExp_endo_transport {β : PowerSeries R} (hβ : PowerSeries.constantCoeff β = 0) :
    β.subst W.formalExp
      = W.formalExp.subst (PowerSeries.subst W.formalExp (W.formalLog.subst β)) := by
  have hExp : PowerSeries.HasSubst W.formalExp :=
    PowerSeries.HasSubst.of_constantCoeff_zero' W.constantCoeff_formalExp
  have hβs : PowerSeries.HasSubst β := PowerSeries.HasSubst.of_constantCoeff_zero' hβ
  have hg : PowerSeries.HasSubst (β.subst W.formalExp) :=
    PowerSeries.HasSubst.of_constantCoeff_zero'
      (PowerSeries.constantCoeff_subst_eq_zero W.constantCoeff_formalExp β hβ)
  rw [PowerSeries.subst_comp_subst_apply hβs hExp W.formalLog,
    W.formalExp_subst_formalLog_subst hg]

/-- **`exp_E(n·z) = [n](exp_E z)` for `n : ℕ`.**  The formal exponential carries multiplication by
`n` on the additive group `𝔾ₐ` to the multiplication-by-`n` series `[n] = W.formalGroup.mulByN n`
of the formal group — the `exp_E`-side dual of `formalLog_subst_mulByN` (#519). -/
theorem formalExp_subst_nsmul_X (n : ℕ) :
    W.formalExp.subst (n • PowerSeries.X : PowerSeries R)
      = (W.formalGroup.mulByN n).subst W.formalExp := by
  have hExp : PowerSeries.HasSubst W.formalExp :=
    PowerSeries.HasSubst.of_constantCoeff_zero' W.constantCoeff_formalExp
  have hscal : PowerSeries.subst W.formalExp (n • W.formalLog)
      = (n • PowerSeries.X : PowerSeries R) := by
    rw [← PowerSeries.coe_substAlgHom hExp, map_nsmul, PowerSeries.coe_substAlgHom hExp,
      W.formalLog_subst_formalExp]
  rw [formalExp_endo_transport W (W.formalGroup.constantCoeff_mulByN n),
    W.formalLog_subst_mulByN n, hscal]

/-- **`exp_E(-z) = i(exp_E z)`.**  The formal exponential carries negation on the additive group
`𝔾ₐ` to the formal inverse series `i = W.formalGroup.formalInv` — the `exp_E`-side dual of
`formalLog_subst_formalInv` (#519). -/
theorem formalExp_subst_neg_X :
    W.formalExp.subst (-PowerSeries.X : PowerSeries R)
      = (FormalGroup.formalInv W.formalGroup).subst W.formalExp := by
  have hExp : PowerSeries.HasSubst W.formalExp :=
    PowerSeries.HasSubst.of_constantCoeff_zero' W.constantCoeff_formalExp
  have hscal : PowerSeries.subst W.formalExp (-W.formalLog)
      = (-PowerSeries.X : PowerSeries R) := by
    rw [← PowerSeries.coe_substAlgHom hExp, map_neg, PowerSeries.coe_substAlgHom hExp,
      W.formalLog_subst_formalExp]
  rw [formalExp_endo_transport W (FormalGroup.constantCoeff_formalInv _),
    W.formalLog_subst_formalInv, hscal]

/-- **`exp_E(n·z) = [n](exp_E z)` for every `n : ℤ`.**  The integer extension of
`formalExp_subst_nsmul_X`, the `exp_E`-side dual of `formalLog_subst_mulByZ` (#519). -/
theorem formalExp_subst_zsmul_X (n : ℤ) :
    W.formalExp.subst (n • PowerSeries.X : PowerSeries R)
      = (W.formalGroup.mulByZ n).subst W.formalExp := by
  have hExp : PowerSeries.HasSubst W.formalExp :=
    PowerSeries.HasSubst.of_constantCoeff_zero' W.constantCoeff_formalExp
  have hscal : PowerSeries.subst W.formalExp (n • W.formalLog)
      = (n • PowerSeries.X : PowerSeries R) := by
    rw [← PowerSeries.coe_substAlgHom hExp, map_zsmul, PowerSeries.coe_substAlgHom hExp,
      W.formalLog_subst_formalExp]
  rw [formalExp_endo_transport W (W.formalGroup.constantCoeff_mulByZ n),
    W.formalLog_subst_mulByZ n, hscal]

end WeierstrassCurve
