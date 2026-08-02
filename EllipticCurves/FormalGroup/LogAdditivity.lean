/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.RingTheory.PowerSeries.Derivative
import EllipticCurves.FormalGroup.GenuineLaw
import EllipticCurves.FormalGroup.Exponential
import EllipticCurves.FormalGroup.MvPowerSeriesCurry
import EllipticCurves.FormalGroup.MvPowerSeriesPderiv

/-!
# Log-additivity of the Weierstrass formal logarithm on the genuine `(z, w)` formal group law

Over a `ℚ`-algebra `R` the formal logarithm `log_E(z) = z + O(z²)`
(`WeierstrassCurve.formalLog`, `EllipticCurves.FormalGroup.Logarithm`) is an isomorphism of the
Weierstrass formal group onto the additive group `𝔾ₐ`.  Concretely (Silverman AEC IV.5,
Proposition 5.2), the **additivity identity**

`log_E(F(z₁, z₂)) = log_E(z₁) + log_E(z₂)`

holds in `MvPowerSeries (Fin 2) R`, where `F = W.formalGroupZW` is the genuine bivariate formal
group law of `EllipticCurves.FormalGroup.GenuineLaw`.  Because `F` has zero constant coefficient
(`constantCoeff_formalGroupZW`), substituting it into the univariate `log_E` needs no pole-freeness:
`log_E(F) := W.formalLog.subst W.formalGroupZW`.

## Strategy (Silverman AEC IV.5, Proposition 5.2)

Over a `ℚ`-algebra, a power series with vanishing derivative and vanishing constant term is `0`.
Writing the **additivity defect**

`Δ := log_E(F) − log_E(z₁) − log_E(z₂)  ∈  MvPowerSeries (Fin 2) R`

(`WeierstrassCurve.formalLogAdditivityDefect`), the identity is `Δ = 0`.  We view `Δ` as a
univariate power series in `z₂` over the coefficient ring `S := R⟦z₁⟧` (a `ℚ`-algebra) via the
currying
ring isomorphism `mvPowerSeriesFinTwoCurry : MvPowerSeries (Fin 2) R ≃+* R⟦z₁⟧⟦z₂⟧` of
`EllipticCurves.FormalGroup.MvPowerSeriesCurry` (inner index `0` = `z₁`, outer index `1` = `z₂`).
By the univariate rigidity principle proved here it suffices to check that the curried defect

* has vanishing `z₂`-derivative — this is the invariant-differential invariance
  `(ω_E ∘ F)·∂_{z₂}F = ω_E(z₂)` (the crux `(★)`), obtained by differentiating `log_E(F)` in `z₂`
  through the chain rule `PowerSeries.derivative_subst` and `derivativeFun_formalLog`, and
* vanishes at `z₂ = 0` — this is the normalisation `F(z₁, 0) = z₁`, whence
  `log_E(F(z₁,0)) − log_E(z₁) = 0`.

## What this file provides

* `PowerSeries.eq_C_of_derivativeFun_eq_zero`, `PowerSeries.eq_zero_of_derivativeFun_eq_zero` :
  the **rigidity principle** over a `ℚ`-algebra — a series with zero derivative equals its constant
  term, and is `0` if in addition its constant term vanishes.  This is the analytic heart of
  Silverman IV.5 and is reusable.
* `WeierstrassCurve.hasSubst_formalGroupZW` : `F` may be substituted into univariate series.
* `WeierstrassCurve.formalLogAdditivityDefect` : the defect `Δ`, and
  `formalLogAdditivityDefect_eq` its defining expansion.
* `WeierstrassCurve.constantCoeff_formalLog_subst` : substituting `F` (or any zero-constant-term
  bivariate series) into `log_E` gives a series with zero constant term.
* `MvPowerSeries.finTwoEvalSndZero` : the `z₂ ↦ 0` evaluation `MvPowerSeries (Fin 2) R →+* R⟦z₁⟧`,
  with `MvPowerSeries.finTwoEvalSndZero_subst` its **substitution naturality**
  `finTwoEvalSndZero (f.subst G) = f.subst (finTwoEvalSndZero G)` — the priority-1 naturality lemma,
  in the form that typechecks (see "Remaining step").
* `WeierstrassCurve.constantCoeff_curry_formalLogAdditivityDefect_of_baseIdentity` : the base fact
  `hbase`, reduced (via the naturality above) to the single formal-group **identity axiom**
  `finTwoEvalSndZero F = X`, i.e. `F(z₁, 0) = z₁`.
* `WeierstrassCurve.formalLog_subst_formalGroupZW_of_curryRigidity` : the **reduction** — the full
  additivity identity, conditional on the two crux facts phrased on the curried defect (vanishing
  `z₂`-constant-coefficient = the base `F(z₁,0)=z₁`, and vanishing `z₂`-derivative = `(★)`).
* `WeierstrassCurve.pderivSnd_formalLog_subst`, `pderivSnd_formalLogAdditivityDefect` : the
  **`z₂`-calculus of the defect**, via the merged substitution chain rule `pderivSnd_subst` — the
  `z₂`-derivative of `Δ` is `(ω_E ∘ F)·∂_{z₂}F − ω_E(z₂)`.
* `WeierstrassCurve.derivativeFun_curry_formalLogAdditivityDefect_of_star` : the derivative fact
  `hderiv`, reduced (via the calculus above) to the single geometric identity `(★)`
  `(ω_E ∘ F)·∂_{z₂}F = ω_E(z₂)`.
* `WeierstrassCurve.formalLog_subst_formalGroupZW_of_identity_star` : the full additivity identity,
  now conditional on *only the two geometric facts* `hF : F(z₁,0)=z₁` and `hstar : (★)` — all the
  analytic rigidity and the `z₂`-calculus are discharged.

## Remaining step

The unconditional `formalLog_subst_formalGroupZW` is *not* proved here.  With
`formalLog_subst_formalGroupZW_of_identity_star`, the two remaining hypotheses are now *purely
geometric* (the rigidity principle and the whole `z₂`-derivative calculus are discharged):

* **`hbase` = `hF`** is reduced by `constantCoeff_curry_formalLogAdditivityDefect_of_baseIdentity`
  to the identity axiom `finTwoEvalSndZero W.formalGroupZW = X` (`F(z₁,0) = z₁`).  For
  `formalGroupZW` this is *not yet available*: it is equivalent to the pending identification
  `formalGroupZW = formalGroupSeries`, whose `z₂ = 0` slice is `z₁` by
  `coeff_formalGroupLaurent_zero`.
  (Note the normalisation coefficients `constantCoeff`, `coeff (single 0 1)`, `coeff (single 1 1)`
  alone do **not** imply `F(z₁,0)=z₁`: e.g. `z₁ + z₂ + c(z₁² + z₂²)` satisfies them yet fails it.)
* **`hderiv` = `hstar` = `(★)`** is the invariant-differential invariance `(ω_E ∘ F)·∂_{z₂}F =
  ω_E(z₂)`.  The `z₂`-calculus obstruction (currying `F` to `R⟦z₁⟧⟦z₂⟧` fails `HasSubst` because the
  `z₂`-constant coefficient `z₁` is non-nilpotent) is now resolved by the merged `MvPowerSeries`
  `z₂`-partial derivative and its chain rule (`EllipticCurves.FormalGroup.MvPowerSeriesPderiv`), so
  `hderiv` is reduced to `hstar` alone by `derivativeFun_curry_formalLogAdditivityDefect_of_star`.
  What remains is the **geometric** identity `(★)` itself, from the merged `(z, w)` structure
  (`formalW_subst_formalGroupZW_fixed`, `formalCubicResidual_root_zero/one`,
  `invariantDifferential_mul_invDiffDen`).  This is the genuine remaining content; no `sorry` used.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.5, Proposition 5.2.
-/

open MvPowerSeries

namespace PowerSeries

variable {S : Type*} [CommRing S] [Algebra ℚ S]

/-- **Rigidity of the formal integral (constant version).** Over a `ℚ`-algebra a power series with
vanishing derivative equals its constant term: `g' = 0 ⟹ g = C g(0)`.  (Integer denominators
`n + 1` are units, so `coeff (n+1) g · (n+1) = 0` forces `coeff (n+1) g = 0`.) -/
theorem eq_C_of_derivativeFun_eq_zero {g : S⟦X⟧} (h : g.derivativeFun = 0) :
    g = C (constantCoeff g) := by
  refine PowerSeries.ext fun n => ?_
  cases n with
  | zero =>
    simp only [coeff_zero_eq_constantCoeff, constantCoeff_C]
  | succ m =>
    have hcoeff : coeff (m + 1) g * ((m : S) + 1) = 0 := by
      have hm := congrArg (coeff m) h
      rwa [coeff_derivativeFun, map_zero] at hm
    have hu : IsUnit ((m : S) + 1) := by
      have hcast : ((m : S) + 1) = algebraMap ℚ S ((m : ℚ) + 1) := by push_cast; ring
      rw [hcast]
      exact (Ne.isUnit (by positivity : ((m : ℚ) + 1) ≠ 0)).map (algebraMap ℚ S)
    rw [coeff_C, if_neg (Nat.succ_ne_zero m)]
    exact (hu.mul_left_eq_zero).mp hcoeff

/-- **Rigidity of the formal integral.** Over a `ℚ`-algebra a power series with vanishing derivative
and vanishing constant term is `0`.  This is the uniqueness half of Silverman AEC IV.5. -/
theorem eq_zero_of_derivativeFun_eq_zero {g : S⟦X⟧} (h : g.derivativeFun = 0)
    (h0 : constantCoeff g = 0) : g = 0 := by
  rw [eq_C_of_derivativeFun_eq_zero h, h0, map_zero]

end PowerSeries

/-! ## Naturality of substitution under the `z₂ ↦ 0` evaluation

The rigidity reduction phrases the two crux facts on the *curried* defect
`mvPowerSeriesFinTwoCurry Δ ∈ R⟦z₁⟧⟦z₂⟧`.  For the base fact `hbase` (the `z₂ = 0` slice) we use the
ring homomorphism `finTwoEvalSndZero : MvPowerSeries (Fin 2) R →+* R⟦z₁⟧` that sets `z₂ = 0`, i.e.
reads the `z₂`-degree-`0` coefficient.  Substitution is *natural* under this evaluation:
`finTwoEvalSndZero (f.subst G) = f.subst (finTwoEvalSndZero G)`, provided `f` may be substituted
into `finTwoEvalSndZero G` (its constant coefficient is nilpotent).  Note that this evaluation
lands in the
*single*-variable ring `R⟦z₁⟧`, where the identity `z₁` has *nilpotent* (indeed zero) constant
coefficient, so `PowerSeries.HasSubst` holds — unlike the full currying to `R⟦z₁⟧⟦z₂⟧`, where the
`z₂`-constant coefficient of `mvPowerSeriesFinTwoCurry F` is the series `z₁`, which is **not**
nilpotent in `R⟦z₁⟧` and hence forbids the univariate substitution
`f.subst (mvPowerSeriesFinTwoCurry F)`.  This is why the derivative crux `(★)` cannot be
discharged by a direct application of
`PowerSeries.derivative_subst`; see the module "Remaining step". -/

namespace MvPowerSeries

variable {R : Type*} [CommRing R]

/-- The **`z₂ ↦ 0` evaluation** `MvPowerSeries (Fin 2) R →+* R⟦z₁⟧`: read off the `z₂`-degree-`0`
slice of a bivariate power series, as the outer constant coefficient of its currying.  It sends the
inner variable `z₁ = X 0` to `X` and the outer variable `z₂ = X 1` to `0`. -/
noncomputable def finTwoEvalSndZero : MvPowerSeries (Fin 2) R →+* PowerSeries R :=
  (PowerSeries.constantCoeff : PowerSeries (PowerSeries R) →+* PowerSeries R).comp
    (mvPowerSeriesFinTwoCurry : MvPowerSeries (Fin 2) R ≃+* _).toRingHom

/-- The `z₁^k`-coefficient of the `z₂ = 0` slice is the `z₁^k z₂^0`-coefficient of the series. -/
@[simp]
theorem coeff_finTwoEvalSndZero (φ : MvPowerSeries (Fin 2) R) (k : ℕ) :
    PowerSeries.coeff k (finTwoEvalSndZero φ) = MvPowerSeries.coeff (Finsupp.single 0 k) φ := by
  rw [finTwoEvalSndZero, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_coeff_mvPowerSeriesFinTwoCurry]
  simp

@[simp]
theorem finTwoEvalSndZero_X_zero :
    finTwoEvalSndZero (X 0 : MvPowerSeries (Fin 2) R) = PowerSeries.X := by
  refine PowerSeries.ext fun k => ?_
  rw [coeff_finTwoEvalSndZero, MvPowerSeries.coeff_X, PowerSeries.coeff_X]
  by_cases hk : k = 1
  · subst hk; simp
  · rw [if_neg (fun h => hk ?_), if_neg hk]
    have := congrArg (fun f => f (0 : Fin 2)) h
    simpa using this

@[simp]
theorem finTwoEvalSndZero_X_one :
    finTwoEvalSndZero (X 1 : MvPowerSeries (Fin 2) R) = 0 := by
  refine PowerSeries.ext fun k => ?_
  rw [coeff_finTwoEvalSndZero, MvPowerSeries.coeff_X, map_zero, if_neg]
  intro h
  have := congrArg (fun f => f (1 : Fin 2)) h
  simp at this

/-- **Naturality of substitution under `z₂ ↦ 0`.** For a univariate series `f` and a bivariate `G`
of zero constant coefficient (so `f.subst G` is defined) whose `z₂ = 0` slice may itself be
substituted into `f`, evaluating `f.subst G` at `z₂ = 0` equals substituting the `z₂ = 0` slice of
`G` into `f`.  Proved coefficientwise from `PowerSeries.coeff_subst`. -/
theorem finTwoEvalSndZero_subst {G : MvPowerSeries (Fin 2) R}
    (hG : MvPowerSeries.constantCoeff G = 0) (f : PowerSeries R)
    (hGX : PowerSeries.HasSubst (finTwoEvalSndZero G)) :
    finTwoEvalSndZero (f.subst G) = f.subst (finTwoEvalSndZero G) := by
  refine PowerSeries.ext fun k => ?_
  rw [coeff_finTwoEvalSndZero,
    PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hG) f (Finsupp.single 0 k),
    PowerSeries.coeff_subst' hGX]
  refine finsum_congr fun d => ?_
  congr 1
  rw [← map_pow, coeff_finTwoEvalSndZero]

end MvPowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- `F = W.formalGroupZW` has zero constant coefficient, hence may be substituted into any
univariate power series. -/
theorem hasSubst_formalGroupZW : PowerSeries.HasSubst W.formalGroupZW :=
  PowerSeries.HasSubst.of_constantCoeff_zero W.constantCoeff_formalGroupZW

/-- Substituting a bivariate series of zero constant coefficient into `log_E` yields a series of
zero constant coefficient (as `log_E(0) = 0`). -/
theorem constantCoeff_formalLog_subst [Algebra ℚ R] {G : MvPowerSeries (Fin 2) R}
    (hG0 : MvPowerSeries.constantCoeff G = 0) :
    MvPowerSeries.constantCoeff (W.formalLog.subst G) = 0 := by
  have hG : PowerSeries.HasSubst G := PowerSeries.HasSubst.of_constantCoeff_zero hG0
  have hzero :
      (fun d => PowerSeries.coeff d W.formalLog • MvPowerSeries.constantCoeff (G ^ d))
        = fun _ => (0 : R) := by
    funext d
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      rw [pow_zero, PowerSeries.coeff_zero_eq_constantCoeff, W.constantCoeff_formalLog, zero_smul]
    · rw [smul_eq_mul, map_pow, hG0, zero_pow hd.ne', mul_zero]
  rw [PowerSeries.constantCoeff_subst hG, hzero, finsum_zero]

/-- **The additivity defect** `Δ = log_E(F) − log_E(z₁) − log_E(z₂) ∈ MvPowerSeries (Fin 2) R`.
The log-additivity identity (Silverman AEC IV.5, Proposition 5.2) is exactly `Δ = 0`. -/
noncomputable def formalLogAdditivityDefect [Algebra ℚ R] : MvPowerSeries (Fin 2) R :=
  W.formalLog.subst W.formalGroupZW - W.formalLog.subst (X 0) - W.formalLog.subst (X 1)

theorem formalLogAdditivityDefect_eq [Algebra ℚ R] :
    W.formalLogAdditivityDefect
      = W.formalLog.subst W.formalGroupZW - W.formalLog.subst (X 0) - W.formalLog.subst (X 1) :=
  rfl

/-- **Base fact `hbase`, reduced to the group-law identity `F(z₁, 0) = z₁`.**  Assuming the identity
axiom in the form `finTwoEvalSndZero F = X` (the `z₂ = 0` slice of the genuine group law `F` is the
inner variable `z₁`), the `z₂`-constant coefficient of the curried additivity defect vanishes: it is
`log_E(z₁) − log_E(z₁) − log_E(0) = 0` by naturality of substitution under `z₂ ↦ 0`
(`MvPowerSeries.finTwoEvalSndZero_subst`).  The remaining input `finTwoEvalSndZero W.formalGroupZW =
X` is the formal-group identity axiom, equivalent to the pending identification `formalGroupZW =
formalGroupSeries` (whose `z₂ = 0` slice is `z₁` by `coeff_formalGroupLaurent_zero`). -/
theorem constantCoeff_curry_formalLogAdditivityDefect_of_baseIdentity [Algebra ℚ R]
    (hF : MvPowerSeries.finTwoEvalSndZero W.formalGroupZW = PowerSeries.X) :
    PowerSeries.constantCoeff
      (mvPowerSeriesFinTwoCurry W.formalLogAdditivityDefect) = 0 := by
  have hrw : PowerSeries.constantCoeff (mvPowerSeriesFinTwoCurry W.formalLogAdditivityDefect)
      = MvPowerSeries.finTwoEvalSndZero W.formalLogAdditivityDefect := by
    rw [MvPowerSeries.finTwoEvalSndZero, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom]
  rw [hrw, formalLogAdditivityDefect_eq, map_sub, map_sub,
    MvPowerSeries.finTwoEvalSndZero_subst W.constantCoeff_formalGroupZW W.formalLog
      (by rw [hF]; exact PowerSeries.HasSubst.X'),
    MvPowerSeries.finTwoEvalSndZero_subst (MvPowerSeries.constantCoeff_X 0) W.formalLog
      (by rw [MvPowerSeries.finTwoEvalSndZero_X_zero]; exact PowerSeries.HasSubst.X'),
    MvPowerSeries.finTwoEvalSndZero_subst (MvPowerSeries.constantCoeff_X 1) W.formalLog
      (by rw [MvPowerSeries.finTwoEvalSndZero_X_one]; exact PowerSeries.HasSubst.zero'),
    hF, MvPowerSeries.finTwoEvalSndZero_X_zero, MvPowerSeries.finTwoEvalSndZero_X_one,
    PowerSeries.X_subst, PowerSeries.subst_zero_of_constantCoeff_zero W.constantCoeff_formalLog,
    sub_self, sub_zero]

/-- **Reduction of log-additivity to the two crux facts** (Silverman AEC IV.5, Proposition 5.2).
Viewing the additivity defect `Δ` as a univariate power series in `z₂` over `S = R⟦z₁⟧` via the
currying isomorphism, the additivity identity `log_E(F) = log_E(z₁) + log_E(z₂)` follows from:

* `hbase` : `Δ` vanishes at `z₂ = 0` (the normalisation `F(z₁, 0) = z₁`), and
* `hderiv` : the `z₂`-derivative of `Δ` vanishes (the invariant-differential invariance `(★)`).

The proof is pure rigidity (`eq_zero_of_derivativeFun_eq_zero`) plus injectivity of the currying
ring isomorphism.  Discharging `hbase`/`hderiv` unconditionally is the remaining step documented in
the module header. -/
theorem formalLog_subst_formalGroupZW_of_curryRigidity [Algebra ℚ R]
    (hbase : PowerSeries.constantCoeff
      (mvPowerSeriesFinTwoCurry W.formalLogAdditivityDefect) = 0)
    (hderiv : (mvPowerSeriesFinTwoCurry W.formalLogAdditivityDefect).derivativeFun = 0) :
    W.formalLog.subst W.formalGroupZW
      = W.formalLog.subst (X 0) + W.formalLog.subst (X 1) := by
  have hcurry : mvPowerSeriesFinTwoCurry W.formalLogAdditivityDefect = 0 :=
    PowerSeries.eq_zero_of_derivativeFun_eq_zero hderiv hbase
  have hA : W.formalLogAdditivityDefect = 0 :=
    mvPowerSeriesFinTwoCurry.injective (by rw [hcurry, map_zero])
  rw [formalLogAdditivityDefect_eq, sub_sub, sub_eq_zero] at hA
  exact hA

/-! ### The `z₂`-derivative side `hderiv`, via the substitution chain rule (`#317` deliverable 3)

The calculus half of `hderiv` — differentiating the additivity defect in `z₂` — is now available
from the merged `MvPowerSeries` `z₂`-partial derivative and its substitution chain rule
(`EllipticCurves.FormalGroup.MvPowerSeriesPderiv`, `pderivSnd`, `pderivSnd_subst`).  It reduces
`hderiv` to the single geometric identity `(★)` `(ω_E ∘ F)·∂_{z₂}F = ω_E(z₂)`, exactly mirroring the
way `constantCoeff_curry_formalLogAdditivityDefect_of_baseIdentity` reduces `hbase` to the identity
axiom `F(z₁,0)=z₁`. -/

/-- **The mixed chain-rule form** (`#317` deliverable 3).  Differentiating a substituted formal
logarithm in `z₂`: for a bivariate `G` of zero constant coefficient,
`∂_{z₂}(log_E(G)) = (ω_E ∘ G)·∂_{z₂}G`.  Immediate from the substitution chain rule
`pderivSnd_subst` and `log_E' = ω_E` (`derivativeFun_formalLog`). -/
theorem pderivSnd_formalLog_subst [Algebra ℚ R] {G : MvPowerSeries (Fin 2) R}
    (hG0 : MvPowerSeries.constantCoeff G = 0) :
    pderivSnd (W.formalLog.subst G) = W.invariantDifferential.subst G * pderivSnd G := by
  rw [pderivSnd_subst hG0, W.derivativeFun_formalLog]

/-- **The `z₂`-partial derivative of the additivity defect, in invariant-differential form.**
`∂_{z₂}Δ = (ω_E ∘ F)·∂_{z₂}F − ω_E(z₂)`: the `log_E(z₁)` term drops (`∂_{z₂}z₁ = 0`,
`pderivSnd_X_zero`) and the `log_E(z₂)` term contributes `ω_E(z₂)` (`∂_{z₂}z₂ = 1`,
`pderivSnd_X_one`). -/
theorem pderivSnd_formalLogAdditivityDefect [Algebra ℚ R] :
    pderivSnd W.formalLogAdditivityDefect
      = W.invariantDifferential.subst W.formalGroupZW * pderivSnd W.formalGroupZW
        - W.invariantDifferential.subst (X 1) := by
  have hsub : ∀ a b : MvPowerSeries (Fin 2) R, pderivSnd (a - b) = pderivSnd a - pderivSnd b := by
    intro a b
    rw [← pderivSndDerivation_apply, ← pderivSndDerivation_apply a, ← pderivSndDerivation_apply b,
      map_sub]
  rw [formalLogAdditivityDefect_eq, hsub, hsub,
    W.pderivSnd_formalLog_subst W.constantCoeff_formalGroupZW,
    W.pderivSnd_formalLog_subst (MvPowerSeries.constantCoeff_X 0),
    W.pderivSnd_formalLog_subst (MvPowerSeries.constantCoeff_X 1),
    pderivSnd_X_zero, mul_zero, sub_zero, pderivSnd_X_one, mul_one]

/-- **Derivative fact `hderiv`, reduced to the geometric invariant-differential identity `(★)`.**
Assuming `(★)` in the form `(ω_E ∘ F)·∂_{z₂}F = ω_E(z₂)`
(`W.invariantDifferential.subst F * pderivSnd F = W.invariantDifferential.subst (X 1)`), the
`z₂`-derivative of the curried additivity defect vanishes.  The `z₂`-derivative on the curried
series is `pderivSnd` transported through the currying iso (`curry_pderivSnd`), and
`pderivSnd_formalLogAdditivityDefect` evaluates it to `(ω_E ∘ F)·∂_{z₂}F − ω_E(z₂)`, which `(★)`
kills.  This is the calculus discharge of `hderiv`; the geometric identity `(★)` itself is the sole
remaining input, to be supplied from the merged `(z, w)` structure. -/
theorem derivativeFun_curry_formalLogAdditivityDefect_of_star [Algebra ℚ R]
    (hstar : W.invariantDifferential.subst W.formalGroupZW * pderivSnd W.formalGroupZW
      = W.invariantDifferential.subst (X 1)) :
    (mvPowerSeriesFinTwoCurry W.formalLogAdditivityDefect).derivativeFun = 0 := by
  rw [← curry_pderivSnd, W.pderivSnd_formalLogAdditivityDefect, hstar, sub_self, map_zero]

/-- **Log-additivity, reduced to the two geometric facts.**  Combining the two reductions, the full
additivity identity `log_E(F) = log_E(z₁) + log_E(z₂)` now follows from *purely geometric* inputs —
all the analytic rigidity and the `z₂`-calculus have been discharged:

* the **identity axiom** `hF : F(z₁, 0) = z₁` (`finTwoEvalSndZero F = X`), and
* the **invariant-differential invariance** `hstar : (ω_E ∘ F)·∂_{z₂}F = ω_E(z₂)` (the crux `(★)`).

These two are the sole remaining content of `#315`; each is to be supplied from the merged
`(z, w)` formal-group structure. -/
theorem formalLog_subst_formalGroupZW_of_identity_star [Algebra ℚ R]
    (hF : MvPowerSeries.finTwoEvalSndZero W.formalGroupZW = PowerSeries.X)
    (hstar : W.invariantDifferential.subst W.formalGroupZW * pderivSnd W.formalGroupZW
      = W.invariantDifferential.subst (X 1)) :
    W.formalLog.subst W.formalGroupZW
      = W.formalLog.subst (X 0) + W.formalLog.subst (X 1) :=
  W.formalLog_subst_formalGroupZW_of_curryRigidity
    (W.constantCoeff_curry_formalLogAdditivityDefect_of_baseIdentity hF)
    (W.derivativeFun_curry_formalLogAdditivityDefect_of_star hstar)

end WeierstrassCurve
