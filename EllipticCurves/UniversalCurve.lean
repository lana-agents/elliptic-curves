/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The universal Weierstrass curve and the specialisation homomorphism

A statement about *every* Weierstrass curve over *every* commutative ring is a statement about
**one** curve over **one** ring, provided the statement is stable under base change.  The curve is
the **universal** one,

`univ : WeierstrassCurve (MvPolynomial (Fin 5) ℤ)`, with `aᵢ = MvPolynomial.X i`,

and the base change is along the **specialisation homomorphism** `W.specialize : S →+* R` sending
`X i` to the corresponding coefficient of `W`, for which `univ.map W.specialize = W`.

`S = MvPolynomial (Fin 5) ℤ` is a characteristic-`0` integral domain, which is what makes the
reduction worth performing: over `S` (or over `S ⊗ ℚ`, or over its fraction field) arguments are
available that are not available over a general `CommRing` — no torsion in the coefficients, no
`2 = 0`, and a fraction field to work in.

## Main definitions

* `WeierstrassCurve.univ` : the universal Weierstrass curve.
* `WeierstrassCurve.specialize` : the specialisation homomorphism `S →+* R` attached to a curve.

## Main results

* `WeierstrassCurve.univ_map_specialize` : `univ.map W.specialize = W`.
* `WeierstrassCurve.specialize_map` : `(W.map f).specialize = f ∘ W.specialize`, the naturality of
  the specialisation homomorphism in the base.  ⚠️ Every `map` lemma proved by descent along `univ`
  needs it — see `EllipticCurves.Torsion.OmegaIntegral`'s `map_ωNum`, which cannot be proved
  without it — and it mentions nothing but `specialize`, so it belongs here rather than at whichever
  consumer happens to want it first.

## Implementation notes

This file imports **only** Mathlib, deliberately.  Both of its consumers — the formal-group
identification in `EllipticCurves.FormalGroup.UniversalIdentification` /
`EllipticCurves.FormalGroup.GenuineLawTransfer`, and the division-polynomial reduction in
`EllipticCurves.Torsion.OmegaUniversal` — sit in unrelated corners of the library, and the
universal curve depends on nothing from either.  Three of the four declarations below were
originally written inside the formal-group files and are unchanged by the move; `specialize_map`
arrived the same way from `EllipticCurves.Torsion.OmegaIntegral`, and is unchanged by it too.
-/

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

/-- The **universal Weierstrass curve** over `S := MvPolynomial (Fin 5) ℤ`, with `aᵢ = X i`.
`S` is a characteristic-`0` integral domain, so its base change carries the unconditional
identification. -/
noncomputable def univ : WeierstrassCurve (MvPolynomial (Fin 5) ℤ) where
  a₁ := MvPolynomial.X 0
  a₂ := MvPolynomial.X 1
  a₃ := MvPolynomial.X 2
  a₄ := MvPolynomial.X 3
  a₆ := MvPolynomial.X 4

/-- The **specialisation homomorphism** `S = MvPolynomial (Fin 5) ℤ →+* R` sending the universal
generators `X 0, …, X 4` to the coefficients `a₁, a₂, a₃, a₄, a₆` of `W`.  Base changing the
universal curve along it recovers `W` (`univ_map_specialize`). -/
noncomputable def specialize (W : WeierstrassCurve R) : MvPolynomial (Fin 5) ℤ →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

/-- Base changing the universal curve along `W.specialize` recovers `W`:
`univ.map W.specialize = W`. -/
theorem univ_map_specialize (W : WeierstrassCurve R) : univ.map W.specialize = W := by
  ext <;>
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, univ, specialize,
      MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]

/-- **The specialisation homomorphism is natural in the base**:
`(W.map f).specialize = f ∘ W.specialize`.

⚠️ This is the lemma that makes a `map` statement provable for an object defined by descent along
`univ`.  If `F W` is built as `(something over univ).map W.specialize`, then `F (W.map f)` and
`(F W).map f` are the two sides of this equation applied to that something, and without it the
descended object has no base-change lemma at all.  The worked consumer is
`EllipticCurves.Torsion.OmegaIntegral`'s `map_ωNum`. -/
lemma specialize_map {S : Type*} [CommRing S] (f : R →+* S) (W : WeierstrassCurve R) :
    (W.map f).specialize = f.comp W.specialize := by
  refine MvPolynomial.ringHom_ext (fun k => ?_) (fun i => ?_)
  · simp [specialize]
  · fin_cases i <;> simp [specialize]

end WeierstrassCurve
