/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Algebra.Polynomial.Derivation
import EllipticCurves.FormalGroup.MvPowerSeriesCurry

/-!
# The `z₂`-partial derivative on `MvPowerSeries (Fin 2) R`

This Mathlib pin provides the univariate formal derivative
`PowerSeries.derivativeFun` / `PowerSeries.derivative : Derivation R R⟦X⟧ R⟦X⟧`
but has **no** partial-derivative operator on `MvPowerSeries`.  For the invariant-differential
argument behind log-additivity of the Weierstrass formal group
(`EllipticCurves.FormalGroup.LogAdditivity`, Silverman AEC IV.5) we need to differentiate a
bivariate series in its *second* variable `z₂`.

We obtain such an operator for free by transporting the univariate `derivativeFun` on the outer
`z₂`-variable across the currying ring isomorphism
`mvPowerSeriesFinTwoCurry : MvPowerSeries (Fin 2) R ≃+* R⟦z₁⟧⟦z₂⟧`
(`EllipticCurves.FormalGroup.MvPowerSeriesCurry`; the *outer* index `1` is `z₂`, the *inner*
index `0` is `z₁`).

## Main definitions and results

* `MvPowerSeries.pderivSnd : MvPowerSeries (Fin 2) R → MvPowerSeries (Fin 2) R` — the `z₂`-partial
  derivative, `curry.symm ∘ derivativeFun ∘ curry`.
* `MvPowerSeries.coeff_coeff_pderivSnd` — its bigraded coefficient formula: the `z₂`-degree `n` is
  bumped to `n + 1` and scaled by `n + 1`.
* Transported `Derivation`-style API: `pderivSnd_add`, `pderivSnd_zero`, `pderivSnd_smul`,
  `pderivSnd_mul` (Leibniz), `pderivSnd_C`, `pderivSnd_X_zero` (`∂_{z₂} z₁ = 0`),
  `pderivSnd_X_one` (`∂_{z₂} z₂ = 1`).
* `MvPowerSeries.pderivSndDerivation : Derivation R (MvPowerSeries (Fin 2) R) _` — `pderivSnd`
  packaged as a genuine `R`-linear `Derivation` (it is `R`-linear, kills `C r` and `X 0`, and sends
  `X 1 ↦ 1`), so the whole `Derivation` API (iterated Leibniz, the power rule, …) is available on it
  for free.
* `MvPowerSeries.pderivSnd_pow` — the power rule `∂_{z₂}(φ ^ n) = n • φ ^ (n-1) • ∂_{z₂}φ`, the
  inductive core of the substitution chain rule.
* `MvPowerSeries.coeff_pderivSnd` — the single-index `MvPowerSeries.coeff` form of the coefficient
  formula.
* `MvPowerSeries.pderivSnd_subst_coe` — the **chain rule, polynomial case**: for `p : R[X]` and a
  substitutable `G`, `∂_{z₂}(p(G)) = p'(G) · ∂_{z₂}G` (via `Derivation.comp_aeval_eq`).
* `MvPowerSeries.pderivSnd_subst` — the **substitution chain rule** in full generality: for a
  univariate `f : R⟦X⟧` and a substitutable bivariate `G` (`constantCoeff G = 0`),
  `∂_{z₂}(f.subst G) = (f.derivativeFun.subst G) · ∂_{z₂}G`.  This is the `Fin 2`-graded analogue of
  `PowerSeries.derivative_subst`, and the key calculus input for the invariant-differential form of
  log-additivity (`EllipticCurves.FormalGroup.LogAdditivity`, `#315`).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.5.
-/

open scoped PowerSeries

namespace MvPowerSeries

variable {R : Type*} [CommRing R]

/-- The **`z₂`-partial derivative** on `MvPowerSeries (Fin 2) R`, defined by transporting the
univariate `PowerSeries.derivativeFun` on the outer (`z₂`) variable across the currying ring
isomorphism `mvPowerSeriesFinTwoCurry`. -/
noncomputable def pderivSnd (φ : MvPowerSeries (Fin 2) R) : MvPowerSeries (Fin 2) R :=
  mvPowerSeriesFinTwoCurry.symm (mvPowerSeriesFinTwoCurry φ).derivativeFun

theorem curry_pderivSnd (φ : MvPowerSeries (Fin 2) R) :
    mvPowerSeriesFinTwoCurry (pderivSnd φ) = (mvPowerSeriesFinTwoCurry φ).derivativeFun := by
  rw [pderivSnd, RingEquiv.apply_symm_apply]

/-- The bigraded coefficient of the `z₂`-partial derivative: the `z₂`-degree `n` is bumped to
`n + 1` and the coefficient scaled by `n + 1`. -/
theorem coeff_coeff_pderivSnd (φ : MvPowerSeries (Fin 2) R) (n m : ℕ) :
    PowerSeries.coeff m (PowerSeries.coeff n (mvPowerSeriesFinTwoCurry (pderivSnd φ)))
      = MvPowerSeries.coeff (Finsupp.single 0 m + Finsupp.single 1 (n + 1)) φ * ((n : R) + 1) := by
  rw [curry_pderivSnd, PowerSeries.coeff_derivativeFun,
    show ((n : PowerSeries R) + 1) = PowerSeries.C ((n : R) + 1) by
      rw [map_add, map_natCast, map_one],
    PowerSeries.coeff_mul_C, coeff_coeff_mvPowerSeriesFinTwoCurry]

/-- Two bivariate series agree iff all their bigraded coefficients agree.  A convenient
extensionality principle through the currying isomorphism. -/
theorem ext_coeff_coeff {φ ψ : MvPowerSeries (Fin 2) R}
    (h : ∀ n m, PowerSeries.coeff m (PowerSeries.coeff n (mvPowerSeriesFinTwoCurry φ))
      = PowerSeries.coeff m (PowerSeries.coeff n (mvPowerSeriesFinTwoCurry ψ))) : φ = ψ := by
  apply mvPowerSeriesFinTwoCurry.injective
  exact PowerSeries.ext fun n => PowerSeries.ext fun m => h n m

theorem pderivSnd_add (φ ψ : MvPowerSeries (Fin 2) R) :
    pderivSnd (φ + ψ) = pderivSnd φ + pderivSnd ψ := by
  rw [pderivSnd, pderivSnd, pderivSnd, map_add, PowerSeries.derivativeFun_add, map_add]

@[simp]
theorem pderivSnd_zero : pderivSnd (0 : MvPowerSeries (Fin 2) R) = 0 := by
  apply ext_coeff_coeff
  intro n m
  rw [coeff_coeff_pderivSnd, map_zero, zero_mul]
  simp

@[simp]
theorem pderivSnd_one : pderivSnd (1 : MvPowerSeries (Fin 2) R) = 0 := by
  rw [pderivSnd, map_one, PowerSeries.derivativeFun_one, map_zero]

/-- **Leibniz rule** for the `z₂`-partial derivative. -/
theorem pderivSnd_mul (φ ψ : MvPowerSeries (Fin 2) R) :
    pderivSnd (φ * ψ) = φ * pderivSnd ψ + ψ * pderivSnd φ := by
  rw [pderivSnd, pderivSnd, pderivSnd, map_mul, PowerSeries.derivativeFun_mul,
    smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, RingEquiv.symm_apply_apply,
    RingEquiv.symm_apply_apply]

/-- Equality criterion for two `Fin 2` bidegrees of the standard shape. -/
private theorem finTwoDeg_eq_iff (m k m' k' : ℕ) :
    (Finsupp.single (0 : Fin 2) m + Finsupp.single 1 k
      = Finsupp.single 0 m' + Finsupp.single 1 k') ↔ (m = m' ∧ k = k') := by
  rw [Finsupp.ext_iff, Fin.forall_fin_two]
  simp

/-- The `z₂`-partial derivative kills constants. -/
@[simp]
theorem pderivSnd_C (r : R) : pderivSnd (MvPowerSeries.C r) = 0 := by
  apply ext_coeff_coeff
  intro n m
  have hne : (Finsupp.single (0 : Fin 2) m + Finsupp.single 1 (n + 1)) ≠ 0 := by
    intro h
    have h1 := DFunLike.congr_fun h (1 : Fin 2)
    simp at h1
  rw [coeff_coeff_pderivSnd, MvPowerSeries.coeff_C, if_neg hne, zero_mul]
  simp

/-- `∂_{z₂} z₁ = 0`. -/
@[simp]
theorem pderivSnd_X_zero :
    pderivSnd (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) = 0 := by
  apply ext_coeff_coeff
  intro n m
  have hne : (Finsupp.single (0 : Fin 2) m + Finsupp.single 1 (n + 1))
      ≠ Finsupp.single 0 1 := by
    intro h
    have h1 := DFunLike.congr_fun h (1 : Fin 2)
    simp at h1
  rw [coeff_coeff_pderivSnd, MvPowerSeries.coeff_X, if_neg hne, zero_mul]
  simp

/-- `∂_{z₂} z₂ = 1`. -/
@[simp]
theorem pderivSnd_X_one :
    pderivSnd (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) = 1 := by
  classical
  apply ext_coeff_coeff
  intro n m
  have hcond : (Finsupp.single (0 : Fin 2) m + Finsupp.single 1 (n + 1) = Finsupp.single 1 1)
      ↔ (m = 0 ∧ n + 1 = 1) := by
    rw [show (Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ)
      = Finsupp.single 0 0 + Finsupp.single 1 1 by simp]
    exact finTwoDeg_eq_iff m (n + 1) 0 1
  rw [coeff_coeff_pderivSnd, map_one, PowerSeries.coeff_one, MvPowerSeries.coeff_X]
  by_cases hn : n = 0
  · subst hn
    by_cases hm : m = 0
    · subst hm
      rw [if_pos (hcond.mpr ⟨rfl, rfl⟩), if_pos rfl, PowerSeries.coeff_one, if_pos rfl]
      simp
    · rw [if_neg (fun h => hm (hcond.mp h).1), if_pos rfl, PowerSeries.coeff_one, if_neg hm,
        zero_mul]
  · rw [if_neg (fun h => absurd (hcond.mp h).2 (by omega)), if_neg hn, map_zero, zero_mul]

/-- `R`-linearity of the `z₂`-partial derivative: `∂_{z₂}(r • φ) = r • ∂_{z₂}φ`. -/
theorem pderivSnd_smul (r : R) (φ : MvPowerSeries (Fin 2) R) :
    pderivSnd (r • φ) = r • pderivSnd φ := by
  rw [smul_eq_C_mul, smul_eq_C_mul, pderivSnd_mul, pderivSnd_C, mul_zero, add_zero]

/-- The **`z₂`-partial derivative packaged as an `R`-linear `Derivation`** on
`MvPowerSeries (Fin 2) R`.  This exposes the full `Derivation` API (iterated Leibniz, the power
rule, `map_smul`, …) on `pderivSnd` for free — in particular it is the natural home for the
inductive core of the substitution chain rule. -/
noncomputable def pderivSndDerivation :
    Derivation R (MvPowerSeries (Fin 2) R) (MvPowerSeries (Fin 2) R) :=
  Derivation.mk'
    { toFun := pderivSnd
      map_add' := pderivSnd_add
      map_smul' := fun r φ => by simpa using pderivSnd_smul r φ }
    (fun a b => by
      change pderivSnd (a * b) = a • pderivSnd b + b • pderivSnd a
      rw [pderivSnd_mul, smul_eq_mul, smul_eq_mul])

@[simp]
theorem pderivSndDerivation_apply (φ : MvPowerSeries (Fin 2) R) :
    pderivSndDerivation φ = pderivSnd φ := rfl

@[simp]
theorem coe_pderivSndDerivation :
    ⇑(pderivSndDerivation : Derivation R (MvPowerSeries (Fin 2) R) _) = pderivSnd := rfl

/-- **Power rule** for the `z₂`-partial derivative: `∂_{z₂}(φ ^ n) = n • φ ^ (n-1) • ∂_{z₂}φ`.
This is the inductive core of the substitution chain rule `∂_{z₂}(f.subst G)
= (f.derivativeFun.subst G) · ∂_{z₂}G`. -/
theorem pderivSnd_pow (φ : MvPowerSeries (Fin 2) R) (n : ℕ) :
    pderivSnd (φ ^ n) = n • φ ^ (n - 1) • pderivSnd φ := by
  have h := pderivSndDerivation.leibniz_pow (a := φ) n
  simpa only [pderivSndDerivation_apply] using h

/-- A single-index coefficient formula for the `z₂`-partial derivative: reading off the bidegree
`(m, n)` coefficient (inner `z₁`-degree `m`, outer `z₂`-degree `n`) bumps the `z₂`-degree to `n + 1`
and scales by `n + 1`.  This is the `MvPowerSeries.coeff` form of `coeff_coeff_pderivSnd`. -/
theorem coeff_pderivSnd (φ : MvPowerSeries (Fin 2) R) (m n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 m + Finsupp.single 1 n) (pderivSnd φ)
      = MvPowerSeries.coeff (Finsupp.single 0 m + Finsupp.single 1 (n + 1)) φ * ((n : R) + 1) := by
  rw [← coeff_coeff_mvPowerSeriesFinTwoCurry, coeff_coeff_pderivSnd]

/-! ### The substitution chain rule

`pderivSnd (f.subst G) = (f.derivativeFun.subst G) * pderivSnd G` for a univariate `f : R⟦X⟧` and a
substitutable bivariate `G` (`constantCoeff G = 0`, i.e. `PowerSeries.HasSubst G`).  We follow the
model of Mathlib's `PowerSeries.derivative_subst`: first the polynomial case via
`Derivation.comp_aeval_eq` on `pderivSndDerivation`, then the general case by a finite-truncation
argument.  (The obstruction noted in `LogAdditivity` — that currying `G` to `R⟦z₁⟧⟦z₂⟧` and applying
`PowerSeries.derivative_subst` fails because the `z₂`-constant coefficient `G(z₁, 0)` is
non-nilpotent — is why the argument is carried out directly in the `Fin 2` grading.) -/

/-- **Chain rule, polynomial case.** For a polynomial `p` and a substitutable `G`, the `z₂`-partial
derivative of `p(G)` obeys the chain rule.  Immediate from `Derivation.comp_aeval_eq` on
`pderivSndDerivation`. -/
theorem pderivSnd_subst_coe {G : MvPowerSeries (Fin 2) R} (hG : PowerSeries.HasSubst G)
    (p : Polynomial R) :
    pderivSnd ((p : R⟦X⟧).subst G)
      = ((p : R⟦X⟧).derivativeFun.subst G) * pderivSnd G := by
  rw [PowerSeries.subst_coe hG, PowerSeries.derivativeFun_coe, PowerSeries.subst_coe hG]
  have h := pderivSndDerivation.comp_aeval_eq (a := G) p
  simpa only [pderivSndDerivation_apply, smul_eq_mul] using h

/-- The total degree of a standard `Fin 2` bidegree. -/
private theorem degree_bidegree (a b : ℕ) :
    Finsupp.degree (Finsupp.single (0 : Fin 2) a + Finsupp.single 1 b) = a + b := by
  rw [map_add, Finsupp.degree_single, Finsupp.degree_single]

/-- **Chain rule for the `z₂`-partial derivative.** For a univariate `f : R⟦X⟧` and a substitutable
bivariate `G` (`constantCoeff G = 0`), differentiating the substitution `f(G)` in `z₂` obeys the
chain rule `∂_{z₂}(f.subst G) = (f'.subst G) · ∂_{z₂}G`.

This is the `Fin 2`-graded analogue of `PowerSeries.derivative_subst`, proved directly in the
bidegree grading (rather than by currying to `R⟦z₁⟧⟦z₂⟧`, which fails: the `z₂`-constant coefficient
`G(z₁, 0)` of the curried `G` is non-nilpotent, so `PowerSeries.HasSubst` — hence
`PowerSeries.derivative_subst` — does not apply).  The strategy follows Mathlib's proof: reduce each
fixed bidegree to a finite truncation of `f`, apply the polynomial case `pderivSnd_subst_coe`, and
match coefficients. -/
theorem pderivSnd_subst {G : MvPowerSeries (Fin 2) R} (hG0 : MvPowerSeries.constantCoeff G = 0)
    (f : R⟦X⟧) :
    pderivSnd (f.subst G) = f.derivativeFun.subst G * pderivSnd G := by
  classical
  have hG : PowerSeries.HasSubst G := PowerSeries.HasSubst.of_constantCoeff_zero hG0
  -- Replacing `h` by a high truncation does not change any coefficient of `h.subst G` in a
  -- bidegree of small total degree, because `G^d` has order `≥ d`.
  have hsubst_trunc : ∀ (h : R⟦X⟧) (e : Fin 2 →₀ ℕ) (M : ℕ), Finsupp.degree e < M →
      MvPowerSeries.coeff e (h.subst G)
        = MvPowerSeries.coeff e ((↑(PowerSeries.trunc M h) : R⟦X⟧).subst G) := by
    intro h e M hM
    rw [PowerSeries.coeff_subst hG, PowerSeries.coeff_subst hG]
    refine finsum_congr fun d => ?_
    by_cases hd : d < M
    · rw [PowerSeries.coeff_coe_trunc_of_lt hd]
    · have hz : MvPowerSeries.coeff e (G ^ d) = 0 := by
        have h1 : Finsupp.degree e < d := by omega
        exact coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast h1)
          (le_order_pow_of_constantCoeff_eq_zero d hG0))
      rw [hz, smul_zero, smul_zero]
  refine MvPowerSeries.ext fun e => ?_
  obtain ⟨m, n, rfl⟩ : ∃ m n, e = Finsupp.single 0 m + Finsupp.single 1 n :=
    ⟨e 0, e 1, by ext i; fin_cases i <;> simp⟩
  set N := m + n + 2 with hN
  -- Coefficients of the two `derivativeFun`s agree up to degree `N - 1`.
  have hder_eq : ∀ d : ℕ, d < N - 1 →
      PowerSeries.coeff d ((↑(PowerSeries.trunc N f) : R⟦X⟧).derivativeFun)
        = PowerSeries.coeff d f.derivativeFun := by
    intro d hd
    rw [PowerSeries.coeff_derivativeFun, PowerSeries.coeff_derivativeFun,
      PowerSeries.coeff_coe_trunc_of_lt (show d + 1 < N by omega)]
  -- Hence substituting the truncated derivative agrees on small bidegrees.
  have hRHSterm : ∀ e₁ : Fin 2 →₀ ℕ, Finsupp.degree e₁ ≤ m + n →
      MvPowerSeries.coeff e₁ ((↑(PowerSeries.trunc N f) : R⟦X⟧).derivativeFun.subst G)
        = MvPowerSeries.coeff e₁ (f.derivativeFun.subst G) := by
    intro e₁ he₁
    rw [PowerSeries.coeff_subst hG, PowerSeries.coeff_subst hG]
    refine finsum_congr fun d => ?_
    by_cases hz : MvPowerSeries.coeff e₁ (G ^ d) = 0
    · rw [hz, smul_zero, smul_zero]
    · have hdle : d ≤ Finsupp.degree e₁ := by
        by_contra hlt
        have hlt' : Finsupp.degree e₁ < d := not_le.mp hlt
        exact hz (coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hlt')
          (le_order_pow_of_constantCoeff_eq_zero d hG0)))
      rw [hder_eq d (by omega)]
  -- Main computation, at bidegree `(m, n)`.
  rw [coeff_pderivSnd,
    hsubst_trunc f (Finsupp.single 0 m + Finsupp.single 1 (n + 1)) N
      (by rw [degree_bidegree]; omega),
    ← coeff_pderivSnd, pderivSnd_subst_coe hG (PowerSeries.trunc N f),
    MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hle : Finsupp.degree p.1 ≤ m + n := by
    have hpm : p.1 + p.2 = Finsupp.single (0 : Fin 2) m + Finsupp.single 1 n := by
      simpa using hp
    have hsum : Finsupp.degree p.1 + Finsupp.degree p.2 = m + n := by
      rw [← map_add Finsupp.degree, hpm, degree_bidegree]
    omega
  rw [hRHSterm p.1 hle]

end MvPowerSeries
