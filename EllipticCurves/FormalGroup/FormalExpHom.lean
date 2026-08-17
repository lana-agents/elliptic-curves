/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FormalGroup.ExponentialHom
import EllipticCurves.FormalGroup.FormalLogHom

/-!
# The formal exponential as an additive homomorphism `𝔾ₐ → Ê(𝔪)`

Let `R` be a `ℚ`-algebra that is `I`-adically complete (`IsAdicComplete I R`; the complete-DVR case
with maximal ideal `𝔪` is `I = 𝔪`).  The ideal `I` carries two additive-group structures on the
same carrier:

* the **additive point group** `𝔾ₐ(𝔪) = ↥I`, ordinary addition of `R` restricted to `I`, and
* the **formal-group point group** `Ê(𝔪) = FormalGroup.OnIdeal W.formalGroup I` whose addition is
  the `I`-adic substitution of the Weierstrass formal group law, `x ⊕ y = F(x, y)`
  (`PointsOnIdeal.lean`).

This file packages the merged, series-level exponential homomorphism (#517,
`WeierstrassCurve.formalExp_subst_add_eq_formalGroupZW_subst`, `ExponentialHom.lean`,
`exp_E(z₁ + z₂) = F(exp_E z₁, exp_E z₂)`) as a genuine **additive-group homomorphism on the point
groups**:

`exp_E : 𝔾ₐ(𝔪) → Ê(𝔪)`,   `exp_E(z₁ + z₂) = exp_E(z₁) ⊕ exp_E(z₂)`,

where the left `+` is ordinary addition in `(↥I, +)` and `⊕` is the formal-group addition.  This is
the group-theoretic incarnation (Silverman AEC IV.6, especially IV.6.4b) of the series identity and
the exp-side dual of `WeierstrassCurve.formalLogHom` (`FormalLogHom.lean`, #521).  The exponential
lands in `I` because `exp_E` has vanishing constant coefficient.  The full isomorphism
`Ê(𝔪) ≅ 𝔾ₐ` (packaging both maps as an `AddEquiv` via the inverse facts) is left elsewhere.

## Main definitions / results

* `WeierstrassCurve.formalExpHom` — the additive homomorphism `𝔾ₐ(𝔪) → Ê(𝔪)`.
* `WeierstrassCurve.formalExpHom_apply` — `(exp_E z).val = adicEval I z.property W.formalExp`.

## References

Silverman, *The Arithmetic of Elliptic Curves*, IV.6.
-/

open MvPowerSeries

noncomputable section

namespace WeierstrassCurve

open PowerSeries FormalGroup

variable {R : Type*} [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R)
    (I : Ideal R) [IsAdicComplete I R]

/-- **The formal exponential as an additive homomorphism `𝔾ₐ(𝔪) → Ê(𝔪)` (Silverman AEC IV.6.4b).**
Over a `ℚ`-algebra `R` that is `I`-adically complete, the `I`-adic evaluation of `exp_E` at points
of the additive point group `𝔾ₐ(𝔪) = ↥I` intertwines ordinary addition with the formal-group
addition `x ⊕ y = F(x, y)` of `Ê(𝔪) = OnIdeal W.formalGroup I`:
`exp_E(z₁ + z₂) = exp_E(z₁) ⊕ exp_E(z₂)`.  Only `map_add'` is discharged (via `AddMonoidHom.mk'`,
the codomain being a group); its proof reduces the merged series identity
`formalExp_subst_add_eq_formalGroupZW_subst` (#517) through the `I`-adic transport law
`adicEvalMv_powerSeries_subst` and the `OnIdeal.fold` workhorse.  The exp-side dual of
`WeierstrassCurve.formalLogHom`. -/
def formalExpHom : (↥I) →+ OnIdeal W.formalGroup I :=
  AddMonoidHom.mk' (fun z => (⟨adicEval I z.property W.formalExp,
      adicEval_mem z.property W.constantCoeff_formalExp⟩ : OnIdeal W.formalGroup I)) <| by
    intro z w
    have hb : ∀ s, (![z.val, w.val] : Fin 2 → R) s ∈ I :=
      OnIdeal.memFin2 I z.property w.property
    have hgcE : PowerSeries.constantCoeff W.formalExp = 0 := W.constantCoeff_formalExp
    have hcc0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) = 0 :=
      MvPowerSeries.constantCoeff_X 0
    have hcc1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) = 0 :=
      MvPowerSeries.constantCoeff_X 1
    -- constant-coefficient and substitutability facts for the two variables and their sum.
    have hgcAdd : MvPowerSeries.constantCoeff
        ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) + MvPowerSeries.X 1) = 0 := by
      rw [map_add, hcc0, hcc1, _root_.add_zero]
    have hgAdd : PowerSeries.HasSubst
        ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) + MvPowerSeries.X 1) :=
      PowerSeries.HasSubst.of_constantCoeff_zero hgcAdd
    have hce0 : MvPowerSeries.constantCoeff
        (W.formalExp.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R)) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero hcc0 W.formalExp hgcE
    have hce1 : MvPowerSeries.constantCoeff
        (W.formalExp.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero hcc1 W.formalExp hgcE
    have he0 : PowerSeries.HasSubst
        (W.formalExp.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R)) :=
      PowerSeries.HasSubst.of_constantCoeff_zero hce0
    have he1 : PowerSeries.HasSubst
        (W.formalExp.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) :=
      PowerSeries.HasSubst.of_constantCoeff_zero hce1
    have hpair : MvPowerSeries.HasSubst
        (![W.formalExp.subst (MvPowerSeries.X 0), W.formalExp.subst (MvPowerSeries.X 1)] :
          Fin 2 → MvPowerSeries (Fin 2) R) := by
      refine MvPowerSeries.hasSubst_of_constantCoeff_nilpotent ?_
      intro s; fin_cases s
      · simpa using he0
      · simpa using he1
    -- The additive point `(z + w).val` seen as the `I`-adic value of `X 0 + X 1` at `![z, w]`.
    have hpt : (z + w).val =
        adicEvalMv I hb ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) + MvPowerSeries.X 1) := by
      rw [map_add, adicEvalMv_X I hb 0, adicEvalMv_X I hb 1]; rfl
    -- Pointwise identification of the evaluated exponentials with the `formalExpHom` values.
    have hval0 : adicEvalMv I hb (W.formalExp.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R))
        = adicEval I z.property W.formalExp := by
      rw [adicEvalMv_powerSeries_subst I hb
          (PowerSeries.HasSubst.of_constantCoeff_zero hcc0) hcc0 W.formalExp,
        adicEval_congr_point I (adicEvalMv_mem I hb hcc0) z.property
          (adicEvalMv_X I hb 0) W.formalExp]
    have hval1 : adicEvalMv I hb (W.formalExp.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R))
        = adicEval I w.property W.formalExp := by
      rw [adicEvalMv_powerSeries_subst I hb
          (PowerSeries.HasSubst.of_constantCoeff_zero hcc1) hcc1 W.formalExp,
        adicEval_congr_point I (adicEvalMv_mem I hb hcc1) w.property
          (adicEvalMv_X I hb 1) W.formalExp]
    apply OnIdeal.ext
    simp only [OnIdeal.add_val]
    -- LHS: `adicEval I (z+w).property W.formalExp`; move the point onto `X 0 + X 1`.
    rw [adicEval_congr_point I (z + w).property (adicEvalMv_mem I hb hgcAdd) hpt W.formalExp,
      ← adicEvalMv_powerSeries_subst I hb hgAdd hgcAdd W.formalExp,
      W.formalExp_subst_add_eq_formalGroupZW_subst, ← W.formalGroup_toPowerSeries,
      OnIdeal.fold hb hpair hce0 hce1]
    -- Both sides evaluate `W.formalGroup.toPowerSeries` at matching two-element families.
    refine adicEvalMv_congr I ?_ _ _ W.formalGroup.toPowerSeries
    funext s; fin_cases s
    · exact hval0
    · exact hval1

@[simp] theorem formalExpHom_apply (z : ↥I) :
    (W.formalExpHom I z).val = adicEval I z.property W.formalExp := rfl

end WeierstrassCurve

end
