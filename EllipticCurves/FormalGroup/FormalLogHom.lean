/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FormalGroup.GroupLawBundleGeneral
import EllipticCurves.FormalGroup.LogAdditivityUnconditional
import EllipticCurves.FormalGroup.PointsOnIdeal
import EllipticCurves.FormalGroup.PointsOnIdealTorsion

/-!
# The formal logarithm as an additive homomorphism `Ê(𝔪) → 𝔾ₐ`

Let `R` be a `ℚ`-algebra that is `I`-adically complete (`IsAdicComplete I R`; the case of a complete
DVR with maximal ideal `𝔪` is `I = 𝔪`).  The ideal `I` carries the abelian group
`Ê(𝔪) = FormalGroup.OnIdeal W.formalGroup I` whose addition is the `I`-adic substitution of the
Weierstrass formal group law, `x ⊕ y = F(x, y)` (`PointsOnIdeal.lean`).  This file packages the
merged, unconditional **series-level log-additivity**
`WeierstrassCurve.formalLog_subst_formalGroupZW` (`LogAdditivityUnconditional.lean`,
`log_E(F(z₁, z₂)) = log_E z₁ + log_E z₂`) as a genuine **additive-group homomorphism on the point
group**:

`log_E : Ê(𝔪) → 𝔾ₐ`,   `log_E(x ⊕ y) = log_E(x) + log_E(y)`,

where the right-hand `+` is ordinary addition in the additive group `𝔾ₐ = (R, +)` and `log_E(x)` is
the `I`-adic evaluation `adicEval I x.property W.formalLog` of the logarithm at `x`.
This is the group-theoretic incarnation (Silverman AEC IV.6, especially IV.6.4a) of the series
identity.  Injectivity / the full isomorphism `Ê(𝔪) ≅ 𝔾ₐ` uses the exponential side and is left
elsewhere.

## Main definitions / results

* `PowerSeries.adicEvalMv_powerSeries_subst` — the transport law `(f ∘ g)(b) = f(g(b))` for a
  *multivariate* substituent `g`; the analogue of the univariate `PowerSeries.adicEval_subst`.
* `WeierstrassCurve.formalLogHom` — the additive homomorphism `Ê(𝔪) → 𝔾ₐ`.
* `WeierstrassCurve.formalLogHom_apply` — `log_E(x) = adicEval I x.property W.formalLog`.

## References

Silverman, *The Arithmetic of Elliptic Curves*, IV.6.
-/

open scoped Topology
open MvPowerSeries

noncomputable section

namespace PowerSeries

variable {A : Type*} [CommRing A]

/-- **Transport / composition law for the `I`-adic evaluation across a multivariate substituent.**
Substituting a multivariate power series `g` (with vanishing constant coefficient) into a univariate
`f` and evaluating `I`-adically at the family `b` equals evaluating `f` at the point `g(b)`:
`(f ∘ g)(b) = f(g(b))`.  This is the multivariate-`g` companion of the univariate
`PowerSeries.adicEval_subst`, both derived from `PowerSeries.adicEvalMv_subst`. -/
theorem adicEvalMv_powerSeries_subst (I : Ideal A) [IsAdicComplete I A] {τ : Type*} [Finite τ]
    {b : τ → A} (hb : ∀ s, b s ∈ I) {g : MvPowerSeries τ A} (hg : PowerSeries.HasSubst g)
    (hgc : MvPowerSeries.constantCoeff g = 0) (f : PowerSeries A) :
    adicEvalMv I hb (f.subst g) = adicEval I (adicEvalMv_mem I hb hgc) f := by
  rw [PowerSeries.subst_def, adicEvalMv_subst I hb hg.const (fun _ => hgc) f,
    adicEval_eq_adicEvalMv I (adicEvalMv_mem I hb hgc)]

end PowerSeries

namespace WeierstrassCurve

open PowerSeries FormalGroup

variable {R : Type*} [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R)
    (I : Ideal R) [IsAdicComplete I R]

/-- **The formal logarithm as an additive homomorphism `Ê(𝔪) → 𝔾ₐ` (Silverman AEC IV.6.4a).**
Over a `ℚ`-algebra `R` that is `I`-adically complete, the `I`-adic evaluation of `log_E` at points
of the formal-group point group `Ê(𝔪) = OnIdeal W.formalGroup I` intertwines the formal-group
addition `x ⊕ y = F(x, y)` with ordinary addition in `𝔾ₐ = (R, +)`:
`log_E(x ⊕ y) = log_E(x) + log_E(y)`.  Only `map_add'` is discharged (via `AddMonoidHom.mk'`,
`R` being a group); its proof reduces the merged series log-additivity
`formalLog_subst_formalGroupZW` through the `I`-adic transport law
`adicEvalMv_powerSeries_subst`. -/
def formalLogHom : OnIdeal W.formalGroup I →+ R :=
  AddMonoidHom.mk' (fun x => adicEval I x.property W.formalLog) <| by
    intro x y
    have hb : ∀ s, (![x.val, y.val] : Fin 2 → R) s ∈ I :=
      OnIdeal.memFin2 I x.property y.property
    have hgc : MvPowerSeries.constantCoeff W.formalGroupZW = 0 := W.constantCoeff_formalGroupZW
    have hg : PowerSeries.HasSubst W.formalGroupZW := PowerSeries.HasSubst.of_constantCoeff_zero hgc
    have hpt : (x + y).val = adicEvalMv I hb W.formalGroupZW := by
      rw [OnIdeal.add_val, W.formalGroup_toPowerSeries]
    rw [adicEval_congr_point I (x + y).property (adicEvalMv_mem I hb hgc) hpt W.formalLog,
      ← adicEvalMv_powerSeries_subst I hb hg hgc W.formalLog,
      W.formalLog_subst_formalGroupZW, map_add,
      adicEvalMv_powerSeries_subst I hb
        (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 0))
        (MvPowerSeries.constantCoeff_X 0) W.formalLog,
      adicEvalMv_powerSeries_subst I hb
        (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1))
        (MvPowerSeries.constantCoeff_X 1) W.formalLog,
      adicEval_congr_point I (adicEvalMv_mem I hb (MvPowerSeries.constantCoeff_X 0))
        x.property (adicEvalMv_X I hb 0) W.formalLog,
      adicEval_congr_point I (adicEvalMv_mem I hb (MvPowerSeries.constantCoeff_X 1))
        y.property (adicEvalMv_X I hb 1) W.formalLog]

@[simp] theorem formalLogHom_apply (x : OnIdeal W.formalGroup I) :
    W.formalLogHom I x = adicEval I x.property W.formalLog := rfl

end WeierstrassCurve

end
