/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Reading a pole-free (iterated) Laurent series as a (bivariate) power series

This is a *curve-agnostic* algebraic toolbox for the Weierstrass formal group law construction
(issue #265). The formal group law is built as an element of the iterated Laurent ring
`(R⸨X⸩)⸨X⸩ = HahnSeries ℤ (HahnSeries ℤ R)` (outer grading `z₂`, inner grading `z₁`); to recognise
it as a genuine bivariate power series one needs two bridges that Mathlib does not provide:

* an **order-`≥0` extraction** turning a Laurent series `x : R⸨X⸩` with no negative-index
  coefficients back into (the coercion of) an honest power series, and
* a **double-coefficient reader** `ofDoubleLaurent` sending an iterated Laurent series to
  `MvPowerSeries (Fin 2) R` by reading off its bigraded coefficients.

Both are stated over an arbitrary `CommRing R`; in particular the extraction lemma applies at the
inner level too (take the coefficient ring to be `R⸨X⸩`).

## Main results

* `HahnSeries.ofPowerSeries_mk_coeff_eq_self` : if `x : R⸨X⸩` has `x.coeff g = 0` for all `g < 0`,
  then `HahnSeries.ofPowerSeries ℤ R (PowerSeries.mk fun n => x.coeff n) = x`.
* `HahnSeries.ofDoubleLaurent` : the reader `(R⸨X⸩)⸨X⸩ → MvPowerSeries (Fin 2) R`,
  `d ↦ (x.coeff (d 1)).coeff (d 0)`, with `coeff_ofDoubleLaurent`,
  `constantCoeff_ofDoubleLaurent`, and the linear-slice lemmas
  `coeff_ofDoubleLaurent_single_zero`, `coeff_ofDoubleLaurent_single_one`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1
  (context; this file itself is pure algebra).
-/

open scoped LaurentSeries

namespace HahnSeries

variable {R : Type*} [CommRing R]

/-! ### Order-`≥0` extraction: a pole-free Laurent series is a coerced power series -/

/-- A Laurent series `x : R⸨X⸩` with no negative-index coefficients is exactly the coercion of the
power series reading off its non-negative coefficients. This is the (missing in Mathlib) partial
inverse to `HahnSeries.ofPowerSeries` on order-`≥0` series. -/
theorem ofPowerSeries_mk_coeff_eq_self {x : R⸨X⸩} (h : ∀ g < 0, x.coeff g = 0) :
    HahnSeries.ofPowerSeries ℤ R (PowerSeries.mk fun n => x.coeff (n : ℤ)) = x := by
  ext g
  rcases lt_or_ge g 0 with hg | hg
  · rw [h g hg, HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
    rintro ⟨n, hn⟩
    simp only [Nat.castOrderEmbedding, OrderEmbedding.coe_ofStrictMono] at hn
    omega
  · lift g to ℕ using hg with n
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk]

/-! ### The double-coefficient reader `(R⸨X⸩)⸨X⸩ → MvPowerSeries (Fin 2) R` -/

/-- Read an iterated Laurent series `x ∈ (R⸨X⸩)⸨X⸩` as a bivariate power series: the coefficient of
`z₁^(d 0) z₂^(d 1)` is the inner `z₁`-coefficient `(x.coeff (d 1)).coeff (d 0)` of `x`. When `x` is
pole-free in both gradings this loses no information. -/
noncomputable def ofDoubleLaurent (x : (R⸨X⸩)⸨X⸩) : MvPowerSeries (Fin 2) R :=
  fun d => (x.coeff (d 1 : ℤ)).coeff (d 0 : ℤ)

@[simp]
theorem coeff_ofDoubleLaurent (x : (R⸨X⸩)⸨X⸩) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (ofDoubleLaurent x) = (x.coeff (d 1 : ℤ)).coeff (d 0 : ℤ) :=
  rfl

/-- The constant coefficient of `ofDoubleLaurent x` is the doubly-`0`-indexed coefficient of `x`. -/
theorem constantCoeff_ofDoubleLaurent (x : (R⸨X⸩)⸨X⸩) :
    MvPowerSeries.constantCoeff (ofDoubleLaurent x) = (x.coeff (0 : ℤ)).coeff (0 : ℤ) := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_ofDoubleLaurent]
  simp

/-- The `z₁`-linear (`z₂`-constant) coefficient of `ofDoubleLaurent x` reads the `z₁`-degree-`k`
part of the order-`0` slice `x.coeff 0`. -/
theorem coeff_ofDoubleLaurent_single_zero (x : (R⸨X⸩)⸨X⸩) (k : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 k) (ofDoubleLaurent x)
      = (x.coeff (0 : ℤ)).coeff (k : ℤ) := by
  rw [coeff_ofDoubleLaurent]
  simp

/-- The `z₂`-linear (`z₁`-constant) coefficient of `ofDoubleLaurent x` reads the `z₁`-degree-`0`
part of the `z₂`-degree-`k` slice `x.coeff k`. -/
theorem coeff_ofDoubleLaurent_single_one (x : (R⸨X⸩)⸨X⸩) (k : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 1 k) (ofDoubleLaurent x)
      = (x.coeff (k : ℤ)).coeff (0 : ℤ) := by
  rw [coeff_ofDoubleLaurent]
  simp

end HahnSeries
