/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FormalGroup.PowerSeriesBridge
import EllipticCurves.FormalGroup.BivariateCoords

/-!
# Base-change naturality of the Laurent embedding `embedDoubleLaurent`

For a ring homomorphism `f : R →+* S`, coefficient-wise application of `f` is a ring homomorphism on
(iterated) Laurent series (`HahnSeries.mapRingHom`, from `BivariateCoords`), and the writer
`embedDoubleLaurent : MvPowerSeries (Fin 2) R → (R⸨X⸩)⸨X⸩` commutes with base change along it. This
is the Laurent-side base-change layer of Step B of the `(z, w) ↔ Laurent` identification transfer
(#323): the universal identification
`embedDoubleLaurent univ.formalGroupZW = univ.formalGroupLaurent` over the domain
`S = MvPolynomial (Fin 5) ℤ` (`embedDoubleLaurent_formalGroupZW_univ`, #52) is pushed to an
arbitrary `CommRing R` along the specialisation hom, and the left-hand side transports via the
naturality proved here (together with the merged MvPowerSeries-side `map_formalGroupZW`, #318).

## Main results

* `HahnSeries.map_ofPowerSeries` :
  `(ofPowerSeries ℤ R g).map f = ofPowerSeries ℤ S (PowerSeries.map f g)`.
* `HahnSeries.iterMapRingHom` : the induced coefficient-wise base change on the iterated Laurent
  ring `(R⸨X⸩)⸨X⸩ →+* (S⸨X⸩)⸨X⸩`, i.e. `mapRingHom (mapRingHom f)`.
* `HahnSeries.iterMapRingHom_embedDoubleLaurent` :
  `iterMapRingHom f (embedDoubleLaurent φ) = embedDoubleLaurent (MvPowerSeries.map f φ)`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1.
-/

open scoped LaurentSeries

namespace PowerSeries

variable {R S : Type*} [CommRing R] [CommRing S]

/-- `PowerSeries.map` of a `PowerSeries.mk` reads off coefficient-wise. -/
theorem map_mk (f : R →+* S) (h : ℕ → R) :
    PowerSeries.map f (PowerSeries.mk h) = PowerSeries.mk (fun n => f (h n)) := by
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk]

end PowerSeries

namespace HahnSeries

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### Base change commutes with `ofPowerSeries` -/

/-- A Laurent series read off a power series has vanishing negative-index coefficients. -/
theorem coeff_ofPowerSeries_of_neg (g : PowerSeries R) {n : ℤ} (hn : n < 0) :
    (ofPowerSeries ℤ R g).coeff n = 0 := by
  rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
  rintro ⟨m, hm⟩
  simp only [Nat.castOrderEmbedding, OrderEmbedding.coe_ofStrictMono] at hm
  omega

/-- **Base change commutes with `ofPowerSeries`.** Reading a power series into `R⸨X⸩` and then
base-changing coefficientwise is the same as base-changing the power series first. -/
theorem map_ofPowerSeries (f : R →+* S) (g : PowerSeries R) :
    (ofPowerSeries ℤ R g).map f = ofPowerSeries ℤ S (PowerSeries.map f g) := by
  ext n
  rcases lt_or_ge n 0 with hn | hn
  · rw [map_coeff, coeff_ofPowerSeries_of_neg g hn, map_zero,
      coeff_ofPowerSeries_of_neg (PowerSeries.map f g) hn]
  · lift n to ℕ using hn with m
    rw [map_coeff, ofPowerSeries_apply_coeff, ofPowerSeries_apply_coeff, PowerSeries.coeff_map]

/-! ### The induced base change on the iterated Laurent ring, and `embedDoubleLaurent` naturality -/

/-- Coefficient-wise base change on the **iterated** Laurent ring `(R⸨X⸩)⸨X⸩ →+* (S⸨X⸩)⸨X⸩`, i.e.
`mapRingHom` (from `BivariateCoords`) applied twice. -/
noncomputable def iterMapRingHom (f : R →+* S) : (R⸨X⸩)⸨X⸩ →+* (S⸨X⸩)⸨X⸩ :=
  mapRingHom (mapRingHom f)

@[simp]
theorem iterMapRingHom_apply (f : R →+* S) (x : (R⸨X⸩)⸨X⸩) :
    iterMapRingHom f x = x.map (mapRingHom f) := rfl

/-- **Base-change naturality of the writer `embedDoubleLaurent`.** Writing a bivariate power series
into the iterated Laurent ring commutes with coefficient-wise base change:
`iterMapRingHom f (embedDoubleLaurent φ) = embedDoubleLaurent (MvPowerSeries.map f φ)`. -/
theorem iterMapRingHom_embedDoubleLaurent (f : R →+* S) (φ : MvPowerSeries (Fin 2) R) :
    iterMapRingHom f (embedDoubleLaurent φ) = embedDoubleLaurent (MvPowerSeries.map f φ) := by
  rw [iterMapRingHom_apply, embedDoubleLaurent, embedDoubleLaurent, map_ofPowerSeries]
  congr 1
  rw [PowerSeries.map_mk]
  refine PowerSeries.ext fun n => ?_
  simp only [PowerSeries.coeff_mk, mapRingHom_apply, map_ofPowerSeries, PowerSeries.map_mk,
    MvPowerSeries.coeff_map]

end HahnSeries
