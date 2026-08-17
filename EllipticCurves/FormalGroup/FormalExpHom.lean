/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FormalGroup.ExponentialHom
import EllipticCurves.FormalGroup.FormalLogHom

/-!
# The formal exponential as an additive homomorphism `𝔾ₐ → Ê(𝔪)` and the isomorphism `Ê(𝔪) ≅ 𝔾ₐ`

Let `R` be a `ℚ`-algebra that is `I`-adically complete (`IsAdicComplete I R`; the complete-DVR case
is `I = 𝔪`).  The ideal `I` carries two abelian-group structures on the same carrier `↥I`:

* the additive group `𝔾ₐ(𝔪) = ↥I` (the submodule `↥I` with ordinary addition), and
* the formal-group point group `Ê(𝔪) = FormalGroup.OnIdeal W.formalGroup I` whose addition is the
  `I`-adic substitution of the Weierstrass formal group law, `x ⊕ y = F(x, y)`.

The merged log-side (`FormalLogHom.lean`, #521) packaged the formal logarithm as an additive
homomorphism `log_E : Ê(𝔪) → 𝔾ₐ`.  This file supplies the **exponential** side and closes the
isomorphism:

* `WeierstrassCurve.formalExpHom : ↥I →+ Ê(𝔪)`, `exp_E(z₁ + z₂) = exp_E(z₁) ⊕ exp_E(z₂)`, the
  group-theoretic incarnation (Silverman AEC IV.6.4a) of the series homomorphism `#517`
  (`formalExp_subst_add_eq_formalGroupZW_subst`);
* `WeierstrassCurve.formalLogHom'`, the refinement of `formalLogHom` landing in `↥I` (its image is
  in `I` because `log_E` has vanishing constant term);
* the mutual-inverse point identities `formalLogHom'_formalExpHom` and `formalExpHom_formalLogHom`,
  transporting the univariate inverse facts `log_E ∘ exp_E = id` / `exp_E ∘ log_E = id` through the
  `I`-adic evaluation; and
* `WeierstrassCurve.formalExpAddEquiv : 𝔾ₐ(𝔪) ≃+ Ê(𝔪)`, the additive isomorphism `Ê(𝔪) ≅ 𝔾ₐ`
  (Silverman AEC IV.6.4b) assembled from `formalExpHom` and its inverse `formalLogHom'`.

## References

Silverman, *The Arithmetic of Elliptic Curves*, IV.6.
-/

open scoped Topology
open MvPowerSeries

noncomputable section

namespace WeierstrassCurve

open PowerSeries FormalGroup

variable {R : Type*} [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R)
    (I : Ideal R) [IsAdicComplete I R]

/-- **The formal exponential as an additive homomorphism `𝔾ₐ → Ê(𝔪)` (Silverman AEC IV.6.4a).**
Over a `ℚ`-algebra `R` that is `I`-adically complete, the `I`-adic evaluation of `exp_E` at points
of the additive group `𝔾ₐ(𝔪) = ↥I` intertwines ordinary addition with the formal-group addition
`x ⊕ y = F(x, y)` of `Ê(𝔪) = OnIdeal W.formalGroup I`: `exp_E(z₁ + z₂) = exp_E(z₁) ⊕ exp_E(z₂)`.
Only `map_add'` is discharged (via `AddMonoidHom.mk'`, `Ê(𝔪)` being a group); its proof reduces the
merged series homomorphism `formalExp_subst_add_eq_formalGroupZW_subst` (#517) through the `I`-adic
transport laws `adicEvalMv_powerSeries_subst` and `OnIdeal.fold`. -/
def formalExpHom : (↥I) →+ OnIdeal W.formalGroup I :=
  AddMonoidHom.mk' (fun z => ⟨adicEval I z.property W.formalExp,
      adicEval_mem z.property W.constantCoeff_formalExp⟩) <| by
    intro z₁ z₂
    apply OnIdeal.ext
    have hb : ∀ s, (![(z₁ : R), (z₂ : R)] : Fin 2 → R) s ∈ I :=
      OnIdeal.memFin2 I z₁.property z₂.property
    have hcX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) = 0 :=
      MvPowerSeries.constantCoeff_X 0
    have hcX1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) = 0 :=
      MvPowerSeries.constantCoeff_X 1
    have hcSum : MvPowerSeries.constantCoeff
        (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) = 0 := by
      rw [map_add, hcX0, hcX1, _root_.add_zero]
    have hgSum : PowerSeries.HasSubst
        (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) :=
      PowerSeries.HasSubst.of_constantCoeff_zero hcSum
    have hcE0 : MvPowerSeries.constantCoeff
        (W.formalExp.subst (MvPowerSeries.X 0) : MvPowerSeries (Fin 2) R) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X 0) W.formalExp
        W.constantCoeff_formalExp
    have hcE1 : MvPowerSeries.constantCoeff
        (W.formalExp.subst (MvPowerSeries.X 1) : MvPowerSeries (Fin 2) R) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X 1) W.formalExp
        W.constantCoeff_formalExp
    have he0 : PowerSeries.HasSubst
        (W.formalExp.subst (MvPowerSeries.X 0) : MvPowerSeries (Fin 2) R) :=
      PowerSeries.HasSubst.of_constantCoeff_zero hcE0
    have he1 : PowerSeries.HasSubst
        (W.formalExp.subst (MvPowerSeries.X 1) : MvPowerSeries (Fin 2) R) :=
      PowerSeries.HasSubst.of_constantCoeff_zero hcE1
    have hpair : MvPowerSeries.HasSubst
        (![W.formalExp.subst (MvPowerSeries.X 0), W.formalExp.subst (MvPowerSeries.X 1)] :
          Fin 2 → MvPowerSeries (Fin 2) R) := by
      refine MvPowerSeries.hasSubst_of_constantCoeff_nilpotent ?_
      intro s; fin_cases s
      · simpa using he0
      · simpa using he1
    -- the two `exp_E(X i)` evaluate `I`-adically to `exp_E(z_i)`
    have he0eq : adicEvalMv I hb (W.formalExp.subst (MvPowerSeries.X 0))
        = adicEval I z₁.property W.formalExp := by
      rw [adicEvalMv_powerSeries_subst I hb
        (PowerSeries.HasSubst.of_constantCoeff_zero hcX0) hcX0 W.formalExp]
      exact adicEval_congr_point I (adicEvalMv_mem I hb hcX0) z₁.property
        (by rw [adicEvalMv_X I hb 0, Matrix.cons_val_zero]) W.formalExp
    have he1eq : adicEvalMv I hb (W.formalExp.subst (MvPowerSeries.X 1))
        = adicEval I z₂.property W.formalExp := by
      rw [adicEvalMv_powerSeries_subst I hb
        (PowerSeries.HasSubst.of_constantCoeff_zero hcX1) hcX1 W.formalExp]
      exact adicEval_congr_point I (adicEvalMv_mem I hb hcX1) z₂.property
        (by rw [adicEvalMv_X I hb 1, Matrix.cons_val_one, Matrix.cons_val_zero]) W.formalExp
    -- LHS: `exp_E(z₁ + z₂)` as an `I`-adic evaluation at the folded point
    have hpt : ((z₁ + z₂ : ↥I) : R)
        = adicEvalMv I hb (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) := by
      rw [map_add, adicEvalMv_X I hb 0, adicEvalMv_X I hb 1]; simp
    have hab : (![adicEval I z₁.property W.formalExp, adicEval I z₂.property W.formalExp] :
          Fin 2 → R)
        = ![adicEvalMv I hb (W.formalExp.subst (MvPowerSeries.X 0)),
            adicEvalMv I hb (W.formalExp.subst (MvPowerSeries.X 1))] := by
      funext s; fin_cases s
      · exact he0eq.symm
      · exact he1eq.symm
    change adicEval I (z₁ + z₂).property W.formalExp = _
    rw [OnIdeal.add_val,
      adicEval_congr_point I (z₁ + z₂).property (adicEvalMv_mem I hb hcSum) hpt W.formalExp,
      ← adicEvalMv_powerSeries_subst I hb hgSum hcSum W.formalExp,
      W.formalExp_subst_add_eq_formalGroupZW_subst, ← W.formalGroup_toPowerSeries,
      OnIdeal.fold hb hpair hcE0 hcE1]
    exact (adicEvalMv_congr I hab _ _ W.formalGroup.toPowerSeries).symm

@[simp] theorem formalExpHom_apply (z : ↥I) :
    (W.formalExpHom I z).val = adicEval I z.property W.formalExp := rfl

/-- **The formal logarithm as an additive homomorphism `Ê(𝔪) → 𝔾ₐ(𝔪) = ↥I`.**  The refinement of
`formalLogHom` (`FormalLogHom.lean`, #521) that lands in the ideal `↥I` rather than all of `R`:
`log_E(x) ∈ I` because `log_E` has vanishing constant term.  This is the inverse map of
`formalExpHom`. -/
def formalLogHom' : OnIdeal W.formalGroup I →+ (↥I) :=
  AddMonoidHom.mk' (fun x => ⟨adicEval I x.property W.formalLog,
      adicEval_mem x.property W.constantCoeff_formalLog⟩) <| by
    intro x y
    apply Subtype.ext
    change adicEval I (x + y).property W.formalLog = _
    rw [AddSubmonoid.coe_add]
    exact map_add (W.formalLogHom I) x y

@[simp] theorem formalLogHom'_apply (x : OnIdeal W.formalGroup I) :
    (W.formalLogHom' I x).val = adicEval I x.property W.formalLog := rfl

/-- **`log_E ∘ exp_E = id` on the point group** (Silverman AEC IV.6.4b, half of the isomorphism).
The `I`-adic transport of the univariate inverse fact `formalLog_subst_formalExp`. -/
theorem formalLogHom'_formalExpHom (z : ↥I) :
    W.formalLogHom' I (W.formalExpHom I z) = z := by
  apply Subtype.ext
  change adicEval I (adicEval_mem z.property W.constantCoeff_formalExp) W.formalLog = (z : R)
  rw [← adicEval_subst I z.property
      (PowerSeries.HasSubst.of_constantCoeff_zero' W.constantCoeff_formalExp)
      W.constantCoeff_formalExp,
    W.formalLog_subst_formalExp, adicEval_X]

/-- **`exp_E ∘ log_E = id` on the point group** (Silverman AEC IV.6.4b, half of the isomorphism).
The `I`-adic transport of the univariate inverse fact `formalExp_subst_formalLog`. -/
theorem formalExpHom_formalLogHom (x : OnIdeal W.formalGroup I) :
    W.formalExpHom I (W.formalLogHom' I x) = x := by
  apply OnIdeal.ext
  change adicEval I (adicEval_mem x.property W.constantCoeff_formalLog) W.formalExp = x.val
  rw [← adicEval_subst I x.property
      (PowerSeries.HasSubst.of_constantCoeff_zero' W.constantCoeff_formalLog)
      W.constantCoeff_formalLog,
    W.formalExp_subst_formalLog, adicEval_X]

/-- **The additive isomorphism `Ê(𝔪) ≅ 𝔾ₐ` (Silverman AEC IV.6.4b).**  Over a `ℚ`-algebra `R` that
is `I`-adically complete, the formal exponential and logarithm are mutually inverse additive-group
isomorphisms between the additive group `𝔾ₐ(𝔪) = ↥I` and the formal-group point group
`Ê(𝔪) = OnIdeal W.formalGroup I`. -/
def formalExpAddEquiv : (↥I) ≃+ OnIdeal W.formalGroup I :=
  AddMonoidHom.toAddEquiv (W.formalExpHom I) (W.formalLogHom' I)
    (AddMonoidHom.ext fun z => W.formalLogHom'_formalExpHom I z)
    (AddMonoidHom.ext fun x => W.formalExpHom_formalLogHom I x)

@[simp] theorem formalExpAddEquiv_apply (z : ↥I) :
    W.formalExpAddEquiv I z = W.formalExpHom I z := rfl

@[simp] theorem formalExpAddEquiv_symm_apply (x : OnIdeal W.formalGroup I) :
    (W.formalExpAddEquiv I).symm x = W.formalLogHom' I x := rfl

end WeierstrassCurve

end
