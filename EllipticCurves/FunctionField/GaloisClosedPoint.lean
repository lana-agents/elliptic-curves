/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.CoordinateRingNormalGeneral
import EllipticCurves.FunctionField.DivisorTransport
import EllipticCurves.FunctionField.GaloisFunctoriality
import EllipticCurves.FunctionField.PrincipalDivisorOfPoint

/-!
# The Galois action on closed points is the Galois action on affine points

`EllipticCurves.FunctionField.DivisorTransport` proves the Galois-equivariance of the divisor,

`div (σ⋆ f) = σ_*(div f)`,   `σ_* = Finsupp.equivMapDomain (mapEquiv (galoisCoordRing σ))`,

and `EllipticCurves.FunctionField.WeilPairingGaloisDivisor` spends it: the Galois-equivariance of
the Weil-pairing element follows from the divisor hypothesis `div g' = σ_*(div g)`. In both files
`σ_*` is an *abstract* permutation of `HeightOneSpectrum (W⁄F).CoordinateRing`, and nothing is known
about where it sends any particular closed point.

This file identifies it on the closed points that come from affine points. The single lemma

`mapEquiv (galoisCoordRing σ) (pointClosedPoint h₂) = pointClosedPoint (equation_algEquiv σ h₂)`

says that `σ_*` sends the closed point of `(x₂, y₂)` to the closed point of `(σ x₂, σ y₂)`: the
action on the spectrum *is* the Galois action on coordinates. It holds because `galoisCoordRing σ`
fixes the two coordinate generators of `F[W⁄F]` and acts by `σ` on the constants
(`EllipticCurves.FunctionField.GaloisFunctionField`), so it carries the ideal `⟨X - x₂, Y - y₂⟩` to
`⟨X - σ x₂, Y - σ y₂⟩`.

## What it buys

* **The divisor hypothesis becomes point-level data.** `divisor_eq_equivMapDomain_of_eq_single`
  turns "`g` is a generator at `P` and `g'` is a generator at `σP`" into the hypothesis
  `WeilPairingGaloisDivisor` consumes; `equivMapDomain_galoisCoordRing_sum_single` does the same
  for a divisor supported on several points, which is the shape `[n]∗(S)` will have.
* **Non-vacuity, for every curve and every `σ`.**
  `mapEquiv_galoisCoordRing_pointClosedPoint_eq_self_iff` says `σ_*` fixes the closed point of
  `(x₂, y₂)` *if and only if* `σ` fixes both coordinates. So `σ_*` is a genuine permutation of
  closed points rather than bookkeeping, and this is settled abstractly rather than on a concrete
  curve. The witness `genX` used in `WeilPairingGaloisDivisor` is σ-fixed and could not settle it.
* **A non-vacuous instance with content.** `exists_generator_divisor_galois` exhibits the
  point-level hypothesis at a genuine nonsingular `n`-torsion point, using the generator of
  `EllipticCurves.FunctionField.PrincipalDivisorOfPoint` and its `σ`-conjugate.
* **The identification, in the named actions.** `EllipticCurves.FunctionField.GaloisFunctoriality`
  packages the same permutation as `galoisPoint σ` and the induced map on divisors as
  `galoisDivisor σ`, and proves they are functorial in `σ`. The last section restates the dictionary
  for those, so that the `Gal(F/S)`-set of affine closed points is identified with the affine
  points: `galoisPoint σ (pointClosedPoint h₂) = pointClosedPoint (σ·h₂)`.

## Scope

Nothing here touches the translation slot: `translateEndo` does not preserve `F[W]`, is not
`ringEquivOfRingEquiv e` for any `e`, and none of the transport applies to it — see the module
docstring of `EllipticCurves.FunctionField.DivisorTransport`. The Galois slot of the Weil pairing
(`#456` deliverable 2) is merged — from rung-5 data at `S` and at `σS` over any base field, and
with nothing carried at `n = 2` **and at `n = 3`** over an algebraically closed one (`#791`/`#825`
supplying the data) — in
`EllipticCurves.FunctionField.WeilPairingGaloisRoot`, and it consumes this file's point-level
dictionary; it does **not** consume `divisor g_S = [n]∗(S)`, which earlier notes here and in
`GaloisFunctoriality` named as its gate. Independently of the pairing, the identity
`[n]∗(σS) = σ_*([n]∗ S)` becomes a statement about points here — by
`equivMapDomain_galoisCoordRing_sum_single` it reduces to "the `σ`-image of the preimage multiset
of `S` is the preimage multiset of `σS`" — and can be proved the moment `[n]∗` on divisors
exists.

Closed points of degree greater than one (those not of the form `pointClosedPoint`) are permuted by
`σ_*` as well; the statements below simply do not mention them, which is the right slice, since the
divisors of the Weil-pairing construction are supported on rational points.

## Main statements

* `WeierstrassCurve.Affine.CoordinateRing.mapEquiv_galoisCoordRing_pointClosedPoint`
* `WeierstrassCurve.Affine.CoordinateRing.mapEquiv_galoisCoordRing_pointClosedPoint_eq_self_iff`
* `WeierstrassCurve.Affine.CoordinateRing.equivMapDomain_galoisCoordRing_single`,
  `_sum_single`
* `WeierstrassCurve.Affine.CoordinateRing.divisor_galoisFunctionField_of_eq_single`
* `WeierstrassCurve.Affine.CoordinateRing.divisor_eq_equivMapDomain_of_eq_single`
* `WeierstrassCurve.Affine.CoordinateRing.exists_generator_divisor_galois`
* `WeierstrassCurve.Affine.CoordinateRing.galoisPoint_pointClosedPoint`,
  `WeierstrassCurve.Affine.CoordinateRing.galoisDivisor_single_pointClosedPoint`

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], II.2 (points and maximal
  ideals), III.8 (the Weil pairing).
-/

open Polynomial IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine.CoordinateRing

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S} {x₂ y₂ : F}

/-! ### The image of the ideal of an affine point -/

/-- `galoisCoordEndo σ` sends the class of `X - x` to the class of `X - σ x`: it fixes the
`X`-generator and acts by `σ` on the constant. -/
@[simp] lemma galoisCoordEndo_XClass (σ : F ≃ₐ[S] F) (x : F) :
    galoisCoordEndo σ (XClass (W⁄F) x) = XClass (W⁄F) (σ x) := by
  have h : XClass (W⁄F) x = AdjoinRoot.of (W⁄F).polynomial (X - C x) := rfl
  have h' : XClass (W⁄F) (σ x) = AdjoinRoot.of (W⁄F).polynomial (X - C (σ x)) := rfl
  rw [h, h', galoisCoordEndo_of, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rfl

/-- `galoisCoordEndo σ` sends the class of `Y - y` to the class of `Y - σ y`: it fixes the
`Y`-generator and acts by `σ` on the constant. -/
@[simp] lemma galoisCoordEndo_YClass (σ : F ≃ₐ[S] F) (y : F) :
    galoisCoordEndo σ (YClass (W⁄F) (C y)) = YClass (W⁄F) (C (σ y)) := by
  have h : YClass (W⁄F) (C y)
      = AdjoinRoot.root (W⁄F).polynomial - AdjoinRoot.of (W⁄F).polynomial (C y) := by
    rw [YClass, map_sub, AdjoinRoot.mk_X]
    rfl
  have h' : YClass (W⁄F) (C (σ y))
      = AdjoinRoot.root (W⁄F).polynomial - AdjoinRoot.of (W⁄F).polynomial (C (σ y)) := by
    rw [YClass, map_sub, AdjoinRoot.mk_X]
    rfl
  rw [h, h', map_sub, galoisCoordEndo_root, galoisCoordEndo_of, Polynomial.map_C]
  rfl

/-- **The ideal of an affine point is carried to the ideal of its `σ`-image.**
`galoisCoordRing σ` maps `⟨X - x, Y - y⟩` onto `⟨X - σ x, Y - σ y⟩`. -/
lemma map_XYIdeal_galoisCoordRing (σ : F ≃ₐ[S] F) (x y : F) :
    (XYIdeal (W⁄F) x (C y)).map (galoisCoordRing σ) = XYIdeal (W⁄F) (σ x) (C (σ y)) := by
  rw [XYIdeal, XYIdeal, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  simp [galoisCoordRing_apply]

/-! ### The dictionary between the two actions -/

/-- **The `σ`-action on closed points is the Galois action on affine points.** The permutation of
`HeightOneSpectrum (W⁄F).CoordinateRing` induced by `galoisCoordRing σ` — the one along which
divisors are transported in `EllipticCurves.FunctionField.DivisorTransport` — sends the closed point
cut out by `(x₂, y₂)` to the closed point cut out by `(σ x₂, σ y₂)`. -/
theorem mapEquiv_galoisCoordRing_pointClosedPoint [W.IsElliptic] (σ : F ≃ₐ[S] F)
    (h₂ : (W⁄F).Equation x₂ y₂) :
    mapEquiv (galoisCoordRing σ) (pointClosedPoint h₂)
      = pointClosedPoint (equation_algEquiv σ h₂) := by
  apply HeightOneSpectrum.ext
  rw [mapEquiv_asIdeal, pointClosedPoint_asIdeal, pointClosedPoint_asIdeal,
    map_XYIdeal_galoisCoordRing]

/-- The closed point of an affine point depends only on the point, not on the proof that it lies on
the curve. -/
lemma pointClosedPoint_congr [W.IsElliptic] {x y x' y' : F} (h : (W⁄F).Equation x y)
    (h' : (W⁄F).Equation x' y') (hx : x = x') (hy : y = y') :
    pointClosedPoint h = pointClosedPoint h' := by
  subst hx; subst hy; rfl

/-- **A closed point determines its affine point.** Two affine points of `W⁄F` cutting out the same
closed point are equal: the ideal `⟨X - x, Y - y⟩` is the kernel of evaluation at `(x, y)`
(`ker_evalEvalHom`), and `X - x` evaluated at `(x', y')` is `x' - x`. -/
theorem pointClosedPoint_inj [W.IsElliptic] {x y x' y' : F} (h : (W⁄F).Equation x y)
    (h' : (W⁄F).Equation x' y') (he : pointClosedPoint h = pointClosedPoint h') :
    x = x' ∧ y = y' := by
  have hI : XYIdeal (W⁄F) x (C y) = XYIdeal (W⁄F) x' (C y') := congrArg HeightOneSpectrum.asIdeal he
  have hx : evalEvalHom h' (XClass (W⁄F) x) = 0 := by
    rw [← RingHom.mem_ker, ker_evalEvalHom, ← hI]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have hy : evalEvalHom h' (YClass (W⁄F) (C y)) = 0 := by
    rw [← RingHom.mem_ker, ker_evalEvalHom, ← hI]
    exact Ideal.subset_span (by simp)
  rw [show XClass (W⁄F) x = mk (W⁄F) (C (X - C x)) from rfl, evalEvalHom_mk, evalEval_C] at hx
  rw [show YClass (W⁄F) (C y) = mk (W⁄F) (Y - C (C y)) from rfl, evalEvalHom_mk] at hy
  simp only [Polynomial.evalEval, eval_sub, eval_X, eval_C] at hx hy
  exact ⟨(sub_eq_zero.mp hx).symm, (sub_eq_zero.mp hy).symm⟩

/-- **The action on closed points is as faithful as the action on coordinates.** `σ` fixes the
closed point of `(x₂, y₂)` if and only if it fixes both coordinates.

This is the non-vacuity certificate for every divisor hypothesis phrased through
`mapEquiv (galoisCoordRing σ)`: the transport is the identity on a closed point exactly when the
Galois element is, so it is a genuine permutation of closed points and not bookkeeping. It holds for
every curve and every `σ`, so no concrete curve is needed to see it. -/
theorem mapEquiv_galoisCoordRing_pointClosedPoint_eq_self_iff [W.IsElliptic] (σ : F ≃ₐ[S] F)
    (h₂ : (W⁄F).Equation x₂ y₂) :
    mapEquiv (galoisCoordRing σ) (pointClosedPoint h₂) = pointClosedPoint h₂
      ↔ σ x₂ = x₂ ∧ σ y₂ = y₂ := by
  rw [mapEquiv_galoisCoordRing_pointClosedPoint]
  exact ⟨fun h => pointClosedPoint_inj _ _ h, fun ⟨hx, hy⟩ => pointClosedPoint_congr _ _ hx hy⟩

/-! ### Divisors supported on affine points -/

/-- The `σ`-transport of the divisor `n·(P)` of a single affine point is `n·(σP)`. -/
theorem equivMapDomain_galoisCoordRing_single [W.IsElliptic] (σ : F ≃ₐ[S] F)
    (h₂ : (W⁄F).Equation x₂ y₂) (n : ℤ) :
    (Finsupp.single (pointClosedPoint h₂) n).equivMapDomain (mapEquiv (galoisCoordRing σ))
      = Finsupp.single (pointClosedPoint (equation_algEquiv σ h₂)) n := by
  rw [Finsupp.equivMapDomain_single, mapEquiv_galoisCoordRing_pointClosedPoint]

/-- The `σ`-transport of a divisor supported on finitely many affine points is the divisor with the
same multiplicities at their `σ`-images.

This is the shape a pullback divisor `[n]∗(S)` will have — a sum over the preimages of `S` — so the
`σ`-equivariance `[n]∗(σS) = σ_*([n]∗ S)` reduces through this lemma to the statement that `σ`
permutes those preimages onto the preimages of `σS`. -/
theorem equivMapDomain_galoisCoordRing_sum_single [W.IsElliptic] {ι : Type*} (σ : F ≃ₐ[S] F)
    (s : Finset ι) {x y : ι → F} (h : ∀ i, (W⁄F).Equation (x i) (y i)) (n : ι → ℤ) :
    (∑ i ∈ s, Finsupp.single (pointClosedPoint (h i)) (n i)).equivMapDomain
        (mapEquiv (galoisCoordRing σ))
      = ∑ i ∈ s, Finsupp.single (pointClosedPoint (equation_algEquiv σ (h i))) (n i) := by
  rw [← Finsupp.domCongr_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Finsupp.domCongr_apply, equivMapDomain_galoisCoordRing_single]

/-- **A function with divisor `n·(P)` has `σ`-conjugate with divisor `n·(σP)`.** -/
theorem divisor_galoisFunctionField_of_eq_single [W.IsElliptic] (σ : F ≃ₐ[S] F)
    (h₂ : (W⁄F).Equation x₂ y₂) {f : (W⁄F).FunctionField} {n : ℤ}
    (hf : divisor (W⁄F) f = Finsupp.single (pointClosedPoint h₂) n) :
    divisor (W⁄F) (galoisFunctionField σ f)
      = Finsupp.single (pointClosedPoint (equation_algEquiv σ h₂)) n := by
  rw [divisor_galoisFunctionField, hf, equivMapDomain_galoisCoordRing_single]

/-- **The divisor hypothesis of the Galois-equivariance of the Weil pairing, from point data.**
If `g` has divisor `n·(P)` and `g'` has divisor `n·(σP)`, then `div g' = σ_*(div g)` — the
hypothesis `weilPairingElt_galois_of_divisor_eq` of
`EllipticCurves.FunctionField.WeilPairingGaloisDivisor` consumes. Note `g'` is *not* required to be
`σ⋆ g`: it is any function with the transported divisor, which is what an intrinsically-constructed
root `g_{σS}` will be. -/
theorem divisor_eq_equivMapDomain_of_eq_single [W.IsElliptic] (σ : F ≃ₐ[S] F)
    (h₂ : (W⁄F).Equation x₂ y₂) {g g' : (W⁄F).FunctionField} {n : ℤ}
    (hg : divisor (W⁄F) g = Finsupp.single (pointClosedPoint h₂) n)
    (hg' : divisor (W⁄F) g' = Finsupp.single (pointClosedPoint (equation_algEquiv σ h₂)) n) :
    divisor (W⁄F) g' = (divisor (W⁄F) g).equivMapDomain (mapEquiv (galoisCoordRing σ)) := by
  rw [hg, hg', equivMapDomain_galoisCoordRing_single]

/-- **The point-level divisor hypothesis is satisfiable at a genuine torsion point.** For a
nonsingular `n`-torsion point `P` of `W⁄F`, the generator `f` of
`EllipticCurves.FunctionField.PrincipalDivisorOfPoint` has divisor `n·(P)`, its `σ`-conjugate has
divisor `n·(σP)`, and the pair satisfies `divisor_eq_equivMapDomain_of_eq_single`.

For `n ≠ 0` those divisors are nonzero (`Finsupp.single_ne_zero`), so the witness is not a constant;
and by `mapEquiv_galoisCoordRing_pointClosedPoint_eq_self_iff` the two closed points involved are
distinct whenever `σ` moves either coordinate of `P`. -/
theorem exists_generator_divisor_galois [W.IsElliptic] [DecidableEq F] (σ : F ≃ₐ[S] F)
    {x y : F} (h : (W⁄F).Nonsingular x y) {n : ℕ} (hP : Point.some x y h ∈ (W⁄F).torsion n) :
    ∃ f g : (W⁄F).FunctionField, f ≠ 0 ∧ g ≠ 0 ∧
      divisor (W⁄F) f = Finsupp.single (pointClosedPoint h.1) (n : ℤ) ∧
      divisor (W⁄F) g = Finsupp.single (pointClosedPoint (equation_algEquiv σ h.1)) (n : ℤ) ∧
      divisor (W⁄F) g = (divisor (W⁄F) f).equivMapDomain (mapEquiv (galoisCoordRing σ)) := by
  obtain ⟨f, hf, hdiv⟩ := exists_generator_divisor_eq_of_torsion h hP
  refine ⟨f, galoisFunctionField σ f, hf, ?_, hdiv, ?_, ?_⟩
  · simpa using (map_ne_zero_iff _ (galoisFunctionField σ).injective).mpr hf
  · exact divisor_galoisFunctionField_of_eq_single σ h.1 hdiv
  · exact divisor_eq_equivMapDomain_of_eq_single σ h.1 hdiv
      (divisor_galoisFunctionField_of_eq_single σ h.1 hdiv)

/-! ### The dictionary in terms of the named Galois actions -/

/-- **The `Gal(F/S)`-set of affine closed points is the `Gal(F/S)`-set of affine points.**
`mapEquiv_galoisCoordRing_pointClosedPoint` stated for the action `galoisPoint` of
`EllipticCurves.FunctionField.GaloisFunctoriality`, which is where the fact that these permutations
compose is proved. -/
theorem galoisPoint_pointClosedPoint [W.IsElliptic] (σ : F ≃ₐ[S] F)
    (h₂ : (W⁄F).Equation x₂ y₂) :
    galoisPoint σ (pointClosedPoint h₂) = pointClosedPoint (equation_algEquiv σ h₂) :=
  mapEquiv_galoisCoordRing_pointClosedPoint σ h₂

/-- The action of `σ` on divisors sends `n·(P)` to `n·(σP)`. -/
theorem galoisDivisor_single_pointClosedPoint [W.IsElliptic] (σ : F ≃ₐ[S] F)
    (h₂ : (W⁄F).Equation x₂ y₂) (n : ℤ) :
    galoisDivisor σ (Finsupp.single (pointClosedPoint h₂) n)
      = Finsupp.single (pointClosedPoint (equation_algEquiv σ h₂)) n := by
  rw [galoisDivisor_apply, Finsupp.equivMapDomain_single, galoisPoint_pointClosedPoint]

end WeierstrassCurve.Affine.CoordinateRing
