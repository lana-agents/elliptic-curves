/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FormalGroup.GroupLawBundleGeneral
import EllipticCurves.FormalGroup.LogAdditivityUnconditional
import EllipticCurves.FormalGroup.MulByZ

/-!
# The `ℤ`-action on the log side: `log_E ∘ [n] = n · log_E` and `log_E ∘ i = -log_E`

Over a `ℚ`-algebra `R`, the formal logarithm `log_E = W.formalLog` of the Weierstrass formal group
law is the `ℤ`-equivariant isomorphism onto the additive group `𝔾ₐ`.  The merged unconditional
log-additivity `log_E(F(z₁, z₂)) = log_E z₁ + log_E z₂`
(`WeierstrassCurve.formalLog_subst_formalGroupZW`) is its additivity; this file records the matching
compatibility with the formal-group `ℤ`-action realised by the multiplication-by-`n` series
`[n] = F.mulByN` / `F.mulByZ` and the formal inverse `i = F.formalInv`:

* `WeierstrassCurve.formalLog_subst_mulByN` : `log_E([n](z)) = n · log_E(z)` for `n : ℕ`;
* `WeierstrassCurve.formalLog_subst_formalInv` : `log_E(i(z)) = -log_E(z)`;
* `WeierstrassCurve.formalLog_subst_mulByZ` : `log_E([n](z)) = n · log_E(z)` for every `n : ℤ`.

Thus `log_E` carries the endomorphism `[n]` of the formal group to multiplication-by-`n` on `𝔾ₐ`,
completing the `Ê(𝔪) ≅ 𝔾ₐ` picture on the logarithm side (Silverman AEC IV.6).

## References

Silverman, *The Arithmetic of Elliptic Curves*, IV.6.
-/

open MvPowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R)

/-- **`log_E([n](z)) = n · log_E(z)` for `n : ℕ`.**  The formal logarithm carries the
multiplication-by-`n` series `[n] = W.formalGroup.mulByN n` to scalar multiplication by `n` on the
additive group `𝔾ₐ` — the `ℤ`-action dual of log-additivity `formalLog_subst_formalGroupZW`. -/
theorem formalLog_subst_mulByN (n : ℕ) :
    W.formalLog.subst (W.formalGroup.mulByN n) = n • W.formalLog := by
  induction n with
  | zero =>
    rw [FormalGroup.mulByN_zero, zero_smul,
      PowerSeries.subst_zero_of_constantCoeff_zero W.constantCoeff_formalLog]
  | succ n ih =>
    have hg : MvPowerSeries.HasSubst
        (![W.formalGroup.mulByN n, PowerSeries.X] : Fin 2 → PowerSeries R) :=
      FormalGroup.hasSubst_cons (W.formalGroup.constantCoeff_mulByN n) (by simp)
    rw [FormalGroup.mulByN_succ]
    simp only [FormalGroup.fgAdd, formalGroup_toPowerSeries]
    rw [W.formalLog_subst_formalGroupZW_subst W.formalLog_subst_formalGroupZW hg]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [ih, PowerSeries.X_subst, succ_nsmul]

/-- **`log_E(i(z)) = -log_E(z)`.**  The formal logarithm carries the formal inverse series
`i = W.formalGroup.formalInv` (which realises negation on the formal group) to negation on the
additive group `𝔾ₐ`. -/
theorem formalLog_subst_formalInv :
    W.formalLog.subst (FormalGroup.formalInv W.formalGroup) = - W.formalLog := by
  have hg : MvPowerSeries.HasSubst
      (![PowerSeries.X, FormalGroup.formalInv W.formalGroup] : Fin 2 → PowerSeries R) :=
    FormalGroup.hasSubst_cons (by simp) (FormalGroup.constantCoeff_formalInv _)
  have key := W.formalLog_subst_formalGroupZW_subst W.formalLog_subst_formalGroupZW hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at key
  rw [PowerSeries.X_subst,
    show W.formalGroupZW.subst (![PowerSeries.X, FormalGroup.formalInv W.formalGroup]) = 0 from by
      rw [← W.formalGroup_toPowerSeries]; exact FormalGroup.subst_formalInv W.formalGroup,
    PowerSeries.subst_zero_of_constantCoeff_zero W.constantCoeff_formalLog] at key
  exact eq_neg_of_add_eq_zero_right key.symm

/-- **`log_E([n](z)) = n · log_E(z)` for every `n : ℤ`.**  The integer extension of
`formalLog_subst_mulByN`, using `formalLog_subst_formalInv` for the negative branch
`[-m] = i ∘ [m]`. -/
theorem formalLog_subst_mulByZ (n : ℤ) :
    W.formalLog.subst (W.formalGroup.mulByZ n) = n • W.formalLog := by
  cases n with
  | ofNat n =>
    rw [FormalGroup.mulByZ_ofNat, W.formalLog_subst_mulByN, Int.ofNat_eq_natCast, natCast_zsmul]
  | negSucc n =>
    have hb := W.formalGroup.hasSubst_mulByN (n + 1)
    rw [FormalGroup.mulByZ_negSucc,
      ← PowerSeries.subst_comp_subst_apply (FormalGroup.hasSubst_formalInv W.formalGroup) hb
        W.formalLog,
      W.formalLog_subst_formalInv,
      show (-W.formalLog).subst (W.formalGroup.mulByN (n + 1))
          = -(W.formalLog.subst (W.formalGroup.mulByN (n + 1))) from by
        rw [← PowerSeries.coe_substAlgHom hb, map_neg, PowerSeries.coe_substAlgHom hb],
      W.formalLog_subst_mulByN (n + 1), negSucc_zsmul]

end WeierstrassCurve
