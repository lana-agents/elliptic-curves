/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FormalGroup.AdicEval
import EllipticCurves.FormalGroup.DividedDifference
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.BigOperators.Finsupp.Fin
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Data.Finset.NatAntidiagonal

/-!
# The divided difference on the diagonal is the formal derivative

For `f ∈ R⟦X⟧`, the first divided difference `Δf = (f(z₁) − f(z₀)) / (z₁ − z₀)`
(`PowerSeries.dividedDiff`, a genuine bivariate power series) specialises on the diagonal
`z₀ = z₁ = x` to the formal derivative `f′(x)`:

`Δf(x, x) = ∑' d, (coeff (d 0 + d 1 + 1) f) · x^(d 0 + d 1) = ∑' n, (n + 1) · coeff (n + 1) f · x^n
          = f′(x)`,

grouping the bidegree sum `d 0 + d 1 = n` (which has `n + 1` solutions) — the algebraic content of
"the tangent slope is the derivative", the missing ingredient for the doubling / duplication case of
the Weierstrass formal group addition law (Silverman AEC IV.1).

## Main result

* `PowerSeries.adicEvalMv_dividedDiff_diagonal` :
  `adicEvalMv I ![x, x] (dividedDiff f) = adicEval I hx (derivativeFun f)`.
-/

open MvPowerSeries

namespace PowerSeries

variable {A : Type*} [CommRing A] (I : Ideal A) [IsAdicComplete I A]

omit [IsAdicComplete I A] in
/-- The two-element diagonal family `![x, x]` lies in `I` when `x ∈ I`. -/
theorem diag_mem {x : A} (hx : x ∈ I) : ∀ s : Fin 2, (![x, x] : Fin 2 → A) s ∈ I := by
  intro s; fin_cases s <;> simpa using hx

/-- **The divided difference on the diagonal is the formal derivative.**  Evaluating the bivariate
divided difference `Δf` at the diagonal point `(x, x)` (with `x ∈ I`, in the `I`-adically complete
ring `A`) yields the `I`-adic evaluation of the formal derivative `f′ = derivativeFun f` at `x`. -/
theorem adicEvalMv_dividedDiff_diagonal {x : A} (hx : x ∈ I) (f : PowerSeries A) :
    adicEvalMv I (diag_mem I hx) (dividedDiff f) = adicEval I hx (derivativeFun f) := by
  classical
  letI : WithIdeal A := ⟨I⟩
  haveI : CompleteSpace A := ((IsAdic.isAdicComplete_iff (I := I) rfl).mp ‹_›).1
  haveI : T2Space A := ((IsAdic.isAdicComplete_iff (I := I) rfl).mp ‹_›).2
  -- Evaluation datum for the diagonal family `![x, x]` in the `I`-adic topology.
  have hev : MvPowerSeries.HasEval (![x, x] : Fin 2 → A) :=
    ⟨fun s ↦ WithIdeal.isTopologicallyNilpotent_of_mem (diag_mem I hx s), by
      rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot⟩
  set L : A := MvPowerSeries.eval₂ (RingHom.id A) (![x, x] : Fin 2 → A) (dividedDiff f) with hLdef
  -- The bivariate evaluation as a convergent sum over `d : Fin 2 →₀ ℕ`.
  have hL0 := MvPowerSeries.hasSum_eval₂ (φ := RingHom.id A) (a := (![x, x] : Fin 2 → A))
    continuous_id hev (dividedDiff f)
  -- Simplify each monomial term: `coeff d (Δf) = coeff (d 0 + d 1 + 1) f` and the product of powers
  -- collapses to `x ^ (d 0 + d 1)`.
  have hterm : (fun d : Fin 2 →₀ ℕ ↦ (RingHom.id A) (MvPowerSeries.coeff d (dividedDiff f)) *
        (d.prod fun s e ↦ (![x, x] : Fin 2 → A) s ^ e)) =
      fun d : Fin 2 →₀ ℕ ↦ coeff (d 0 + d 1 + 1) f * x ^ (d 0 + d 1) := by
    funext d
    rw [coeff_dividedDiff, RingHom.id_apply, Finsupp.prod_fintype _ _ (fun i ↦ pow_zero _),
      Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← pow_add]
  rw [hterm] at hL0
  have hL : HasSum (fun d : Fin 2 →₀ ℕ ↦ coeff (d 0 + d 1 + 1) f * x ^ (d 0 + d 1)) L := hL0
  -- Reindex `Fin 2 →₀ ℕ ≃ ℕ × ℕ` via `d ↦ (d 0, d 1)`.
  have hP : HasSum (fun p : ℕ × ℕ ↦ coeff (p.1 + p.2 + 1) f * x ^ (p.1 + p.2)) L := by
    rw [← Equiv.hasSum_iff (finTwoArrowEquiv' ℕ)]
    exact hL
  -- Reindex `ℕ × ℕ ≃ Σ n, antidiagonal n` and identify the summand as constant on each fibre.
  have hfun : ((fun p : ℕ × ℕ ↦ coeff (p.1 + p.2 + 1) f * x ^ (p.1 + p.2)) ∘
        ⇑(Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ))) =
      fun nkl : Σ n : ℕ, ↥(Finset.antidiagonal n) ↦ coeff (nkl.1 + 1) f * x ^ nkl.1 := by
    funext nkl
    obtain ⟨n, kl, hkl⟩ := nkl
    rw [Finset.mem_antidiagonal] at hkl
    simp only [Function.comp_apply,
      Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply, hkl]
  rw [← Equiv.hasSum_iff (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)), hfun] at hP
  -- Each fibre `antidiagonal n` has `n + 1` elements, and the summand is constant on it.
  have hfib : ∀ n : ℕ, HasSum (fun _ : ↥(Finset.antidiagonal n) ↦ coeff (n + 1) f * x ^ n)
      ((n + 1) • (coeff (n + 1) f * x ^ n)) := by
    intro n
    have h := hasSum_fintype (fun _ : ↥(Finset.antidiagonal n) ↦ coeff (n + 1) f * x ^ n)
    rwa [Finset.sum_const, Finset.card_univ, Fintype.card_coe, Finset.Nat.card_antidiagonal] at h
  -- Group the fibres: the total sum splits as `∑' n, (n + 1) • (coeff (n + 1) f * x ^ n)`.
  have hsig := hP.sigma hfib
  -- Match the derivative coefficient shape.
  have hfun2 : (fun n : ℕ ↦ (n + 1) • (coeff (n + 1) f * x ^ n)) =
      fun n : ℕ ↦ coeff n (derivativeFun f) * x ^ n := by
    funext n
    rw [coeff_derivativeFun, nsmul_eq_mul]
    push_cast
    ring
  rw [hfun2] at hsig
  -- The right-hand side, `f′(x)`, as a convergent sum with the *same* summand.
  have hxnil : PowerSeries.HasEval x := WithIdeal.isTopologicallyNilpotent_of_mem hx
  have hR := PowerSeries.hasSum_eval₂ (φ := RingHom.id A) (a := x) continuous_id hxnil
    (derivativeFun f)
  simp only [RingHom.id_apply] at hR
  -- Conclude by uniqueness of sums.
  rw [coe_adicEvalMv I (diag_mem I hx), coe_adicEval hx, ← hLdef]
  exact hsig.unique hR

end PowerSeries
