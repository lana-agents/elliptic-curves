/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FormalGroup.FormalGroupLaurent
import EllipticCurves.FormalGroup.PowerSeriesBridge

/-!
# Extracting the Weierstrass formal group law as a bivariate power series

Building on the Laurent element `F_E = W.formalGroupLaurent = -x₃·y₃⁻¹ ∈ R⸨z₁⸩⸨z₂⸩`
(`EllipticCurves.FormalGroup.FormalGroupLaurent`) and the curve-agnostic bridge
`HahnSeries.ofDoubleLaurent : (R⸨X⸩)⸨X⸩ → MvPowerSeries (Fin 2) R`
(`EllipticCurves.FormalGroup.PowerSeriesBridge`), this file reads `F_E` off as a genuine bivariate
power series

`W.formalGroupSeries : MvPowerSeries (Fin 2) R`,

establishes the **load-bearing leading identity** `F_E.coeff 0 = z₁` — the `z₂`-degree-`0` slice of
`F_E` is exactly the inner variable `z₁` — and derives the two `z₁`-side normalisation coefficients
of `formalGroupSeries` from it:

* `constantCoeff (F_E) = 0`,
* the `z₁`-linear coefficient `coeff (single 0 1) = 1`.

Together with the `z₂`-linear coefficient `coeff (single 1 1) = 1` (which requires the inner
`z₂`-slice `F_E.coeff 1`) these are the normalisation axioms `F_E(z₁,z₂) = z₁ + z₂ + ⋯` of a formal
group law (Silverman AEC IV.1, Theorem 1.1).

## Main definitions

* `WeierstrassCurve.formalGroupSeries` : the Weierstrass formal group law read as
  `MvPowerSeries (Fin 2) R`.

## Main results

* `WeierstrassCurve.coeff_formalGroupSeries` : the bigraded coefficient bridge
  `coeff d formalGroupSeries = (F_E.coeff (d 1)).coeff (d 0)`.
* `WeierstrassCurve.coeff_formalGroupLaurent_zero` : the leading identity `F_E.coeff 0 = z₁`.
* `WeierstrassCurve.constantCoeff_formalGroupSeries` : `constantCoeff formalGroupSeries = 0`.
* `WeierstrassCurve.coeff_formalGroupSeries_single_zero` :
  `coeff (single 0 1) formalGroupSeries = 1`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1.
-/

open scoped LaurentSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### The load-bearing leading identity `F_E.coeff 0 = z₁` -/

/-- The `z₂`-order of `x₃` and `y₃`, and of `F_E`, are all `0` over a nontrivial ring, so the
associated `HahnSeries.order` (the `ℤ`-valued order) is `0`. -/
private lemma order_formalYThree [Nontrivial R] : W.formalYThree.order = 0 := by
  have hne : W.formalYThree ≠ 0 :=
    HahnSeries.orderTop_ne_top.mp (by rw [W.orderTop_formalYThree]; exact WithTop.zero_ne_top)
  have h := HahnSeries.order_eq_orderTop_of_ne_zero hne
  rw [W.orderTop_formalYThree] at h
  exact_mod_cast h

private lemma order_formalXThree [Nontrivial R] : W.formalXThree.order = 0 := by
  have hne : W.formalXThree ≠ 0 :=
    HahnSeries.orderTop_ne_top.mp (by rw [W.orderTop_formalXThree]; exact WithTop.zero_ne_top)
  have h := HahnSeries.order_eq_orderTop_of_ne_zero hne
  rw [W.orderTop_formalXThree] at h
  exact_mod_cast h

private lemma order_formalGroupLaurent [Nontrivial R] : W.formalGroupLaurent.order = 0 := by
  have hne : W.formalGroupLaurent ≠ 0 :=
    HahnSeries.orderTop_ne_top.mp
      (by rw [W.orderTop_formalGroupLaurent]; exact WithTop.zero_ne_top)
  have h := HahnSeries.order_eq_orderTop_of_ne_zero hne
  rw [W.orderTop_formalGroupLaurent] at h
  exact_mod_cast h

/-- **The load-bearing leading identity.** The `z₂`-degree-`0` slice of the formal group law `F_E`
is exactly the inner variable `z₁ = single 1 1 ∈ R⸨z₁⸩`.

Take the `z₂`-order-`0` leading coefficient of the defining identity `F_E · y₃ = -x₃`: both `F_E`
and `y₃` have `z₂`-order `0`, so the `z₂`-degree-`0` coefficient of the product is
`F_E.coeff 0 · y₃.coeff 0 = F_E.coeff 0 · y(z₁)` (`leadingCoeff_formalYThree`), while the right side
is `-x₃.coeff 0 = -x(z₁)` (`leadingCoeff_formalXThree`). Since `z₁ · y(z₁) = -x(z₁)`
(`single_one_mul_formalY`) and `y(z₁)` is a unit (`isUnit_formalY`), cancelling `y(z₁)` gives
`F_E.coeff 0 = z₁`. This pins the inner behaviour of the leading `z₂`-slice to a pole-free
monomial. -/
theorem coeff_formalGroupLaurent_zero :
    W.formalGroupLaurent.coeff 0 = HahnSeries.single (1 : ℤ) 1 := by
  obtain _ | _ := subsingleton_or_nontrivial R
  · exact Subsingleton.elim _ _
  -- The `z₂`-degree-`0` coefficient of `F_E · y₃` is the product of the two leading coefficients.
  have hx3 : W.formalXThree.coeff 0 = W.formalX := by
    rw [← W.order_formalXThree, ← HahnSeries.leadingCoeff_eq, W.leadingCoeff_formalXThree]
  have hmul := HahnSeries.coeff_mul_order_add_order W.formalGroupLaurent W.formalYThree
  rw [W.order_formalGroupLaurent, W.order_formalYThree, add_zero, W.leadingCoeff_formalYThree,
    HahnSeries.leadingCoeff_eq, W.order_formalGroupLaurent,
    W.formalGroupLaurent_mul_formalYThree, HahnSeries.coeff_neg, hx3] at hmul
  -- `hmul : -x(z₁) = F_E.coeff 0 · y(z₁)`; combine with `z₁ · y(z₁) = -x(z₁)` and cancel `y(z₁)`.
  have hkey : W.formalGroupLaurent.coeff 0 * W.formalY
      = HahnSeries.single (1 : ℤ) 1 * W.formalY := by
    rw [← hmul, W.single_one_mul_formalY]
  exact (W.isUnit_formalY.mul_left_inj).mp hkey

/-! ### The formal group series and its `z₁`-side normalisation coefficients -/

/-- The **Weierstrass formal group law** read as a genuine bivariate power series
`MvPowerSeries (Fin 2) R`, via the bridge `HahnSeries.ofDoubleLaurent` applied to the Laurent
element `F_E = W.formalGroupLaurent`. (Silverman AEC IV.1, Theorem 1.1.) -/
noncomputable def formalGroupSeries : MvPowerSeries (Fin 2) R :=
  HahnSeries.ofDoubleLaurent W.formalGroupLaurent

/-- The bigraded coefficient bridge: the coefficient of `z₁^(d 0) z₂^(d 1)` in `formalGroupSeries`
is the inner `z₁`-coefficient `(F_E.coeff (d 1)).coeff (d 0)` of the Laurent element `F_E`. -/
theorem coeff_formalGroupSeries (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d W.formalGroupSeries
      = (W.formalGroupLaurent.coeff (d 1 : ℤ)).coeff (d 0 : ℤ) :=
  HahnSeries.coeff_ofDoubleLaurent _ _

/-- **Normalisation axiom (constant term).** `F_E` has zero constant term: `constantCoeff = 0`. -/
theorem constantCoeff_formalGroupSeries :
    MvPowerSeries.constantCoeff W.formalGroupSeries = 0 := by
  rw [formalGroupSeries, HahnSeries.constantCoeff_ofDoubleLaurent, W.coeff_formalGroupLaurent_zero,
    HahnSeries.coeff_single_of_ne (by norm_num)]

/-- **Normalisation axiom (`z₁`-linear term).** The coefficient of `z₁` in `F_E` is `1`. -/
theorem coeff_formalGroupSeries_single_zero :
    MvPowerSeries.coeff (Finsupp.single 0 1) W.formalGroupSeries = 1 := by
  rw [formalGroupSeries, HahnSeries.coeff_ofDoubleLaurent_single_zero,
    W.coeff_formalGroupLaurent_zero, Nat.cast_one, HahnSeries.coeff_single_same]

end WeierstrassCurve
