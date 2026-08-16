/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.FieldTheory.IsAlgClosed.Basic
import EllipticCurves.FunctionField.LocalRingUniformizer
import EllipticCurves.FunctionField.PointClosedPoint

/-!
# The coordinate ring of an elliptic curve over an algebraically closed field is Dedekind

Let `W` be an elliptic curve (`[W.IsElliptic]`) over an **algebraically closed** field `F`. This
file discharges the `#396` Part A normality crux over `F̄`: the affine coordinate ring `F[W]` is
integrally closed, hence a Dedekind domain.

## Strategy

`IsIntegrallyClosed.of_localization_maximal` reduces integral-closedness of the domain `F[W]` to:
for every nonzero maximal ideal `p`, the localization `Localization.AtPrime p` is integrally closed.
Two ingredients combine:

* **Classification of maximal ideals** (`exists_equation_and_eq_XYIdeal_of_isMaximal`): over an
  algebraically closed field every maximal ideal of `F[W]` is `XYIdeal W a (C b) = ⟨X - a, Y - b⟩`
  for a point `(a, b)` on the curve. The residue field `F[W] ⧸ m` is a field that is a
  finitely-generated `F`-algebra, hence (Zariski's lemma,
  `finite_of_finite_type_of_isJacobsonRing`) finite — and therefore integral — over `F`; algebraic
  closedness (`IsAlgClosed.algebraMap_bijective_of_isIntegral`) then makes `F → F[W] ⧸ m` an
  isomorphism, giving an `F`-algebra section `φ : F[W] →ₐ[F] F` with kernel `m`. Reading off
  `a := φ (X)`, `b := φ (Y)` and using `Polynomial.aevalAevalEquiv`, the relation `φ (W.polynomial)
  = 0` becomes `W.Equation a b`, and `XYIdeal W a (C b) ≤ m`; both are maximal, so they are equal.

* **Local principality** (`maximalIdeal_isPrincipal_of_nonsingular`, the `#469` milestone): at such
  a point the maximal ideal of the localization is principal, so by the discrete-valuation-ring
  TFAE the localization is integrally closed.

## Main results

* `exists_equation_and_eq_XYIdeal_of_isMaximal`: the maximal-ideal classification over `F̄`.
* `isIntegrallyClosed_of_isAlgClosed`: `IsIntegrallyClosed W.CoordinateRing`.
* `isDedekindDomain_of_isAlgClosed`: `IsDedekindDomain W.CoordinateRing`.

The general (non-algebraically-closed) base field needs the finite-residue-field closed points or an
integral-closedness descent along `F[W] → F̄[W]`, and is left to a follow-on.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine.CoordinateRing

variable {F : Type*} [Field F] [IsAlgClosed F]
    {W : WeierstrassCurve.Affine F} [W.IsElliptic]

omit [W.IsElliptic] in
/-- **Classification of maximal ideals over an algebraically closed field.** Every maximal ideal of
the affine coordinate ring `F[W]` of an elliptic curve over an algebraically closed field `F` is
`XYIdeal W a (C b) = ⟨X - a, Y - b⟩` for a point `(a, b)` lying on the curve. -/
theorem exists_equation_and_eq_XYIdeal_of_isMaximal (m : Ideal W.CoordinateRing)
    [hm : m.IsMaximal] : ∃ a b : F, W.Equation a b ∧ m = XYIdeal W a (C b) := by
  -- The residue field `F[W] ⧸ m`.
  letI : Field (W.CoordinateRing ⧸ m) := Ideal.Quotient.field m
  -- `F[W]` is of finite type over `F` (finite over `F[X]`, which is finite type over `F`).
  haveI : Algebra.FiniteType F W.CoordinateRing :=
    Algebra.FiniteType.trans (S := F[X]) inferInstance inferInstance
  haveI : Algebra.FiniteType F (W.CoordinateRing ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F m)
      (Ideal.Quotient.mkₐ_surjective F m)
  -- Zariski's lemma: the residue field is finite, hence integral, over `F`.
  haveI : Module.Finite F (W.CoordinateRing ⧸ m) :=
    finite_of_finite_type_of_isJacobsonRing F (W.CoordinateRing ⧸ m)
  -- `F` algebraically closed ⇒ `F → F[W] ⧸ m` is an isomorphism.
  have hbij : Function.Bijective (algebraMap F (W.CoordinateRing ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : F ≃ₐ[F] W.CoordinateRing ⧸ m :=
    AlgEquiv.ofBijective (Algebra.ofId F (W.CoordinateRing ⧸ m)) hbij
  -- The `F`-algebra section with kernel `m`.
  let φ : W.CoordinateRing →ₐ[F] F := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ F m)
  have hker : RingHom.ker (φ : W.CoordinateRing →+* F) = m := by
    have hinj : Function.Injective ⇑(e.symm.toAlgHom : (W.CoordinateRing ⧸ m) →+* F) :=
      e.symm.injective
    change RingHom.ker ((e.symm.toAlgHom : (W.CoordinateRing ⧸ m) →+* F).comp
      ((Ideal.Quotient.mkₐ F m : W.CoordinateRing →+* W.CoordinateRing ⧸ m))) = m
    rw [RingHom.ker_comp_of_injective _ hinj, Ideal.Quotient.mkₐ_ker]
  -- Pull `φ` back to a bivariate `F`-algebra hom and read off the point via `aevalAevalEquiv`.
  let ψ : F[X][Y] →ₐ[F] F := φ.comp ((AdjoinRoot.mkₐ W.polynomial).restrictScalars F)
  have hψmk : ∀ g : F[X][Y], φ (AdjoinRoot.mk W.polynomial g) = ψ g := fun g => rfl
  set a : F := ψ (C X) with ha
  set b : F := ψ (Y : F[X][Y]) with hb
  have hψeval : ∀ g : F[X][Y], ψ g = g.evalEval a b := by
    have hrepr : Polynomial.aevalAeval a b = ψ := by
      have := (Polynomial.aevalAevalEquiv F F).apply_symm_apply ψ
      simpa [ha, hb, Polynomial.aevalAevalEquiv_apply] using this
    intro g
    rw [← hrepr, Polynomial.coe_aevalAeval_eq_evalEval]
  -- `W.Equation a b`: `W.polynomial ↦ 0` under `φ ∘ mk`.
  have hEq : W.Equation a b := by
    have h0 : ψ W.polynomial = 0 := by
      rw [← hψmk W.polynomial, AdjoinRoot.mk_self, map_zero]
    rw [Equation, ← hψeval W.polynomial, h0]
  refine ⟨a, b, hEq, ?_⟩
  -- `XYIdeal W a (C b) ≤ m` since both generators lie in `ker φ = m`.
  have hXmem : XClass W a ∈ m := by
    rw [← hker, RingHom.mem_ker]
    change φ (AdjoinRoot.mk W.polynomial (C (X - C a))) = 0
    rw [hψmk, hψeval, Polynomial.evalEval_C, eval_sub, eval_X, eval_C, sub_self]
  have hYmem : YClass W (C b) ∈ m := by
    rw [← hker, RingHom.mem_ker]
    change φ (AdjoinRoot.mk W.polynomial (Y - C (C b))) = 0
    rw [map_sub, map_sub, hψmk, hψmk, hψeval, hψeval, Polynomial.evalEval_X,
      Polynomial.evalEval_C, eval_C, sub_self]
  have hle : XYIdeal W a (C b) ≤ m := by
    rw [XYIdeal, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hXmem, hYmem⟩
  exact ((XYIdeal_isMaximal hEq).eq_of_le hm.ne_top hle).symm

/-- **The coordinate ring of an elliptic curve over an algebraically closed field is integrally
closed.** -/
theorem isIntegrallyClosed_of_isAlgClosed : IsIntegrallyClosed W.CoordinateRing := by
  refine IsIntegrallyClosed.of_localization_maximal fun p hp0 hp => ?_
  -- Classify `p` as a curve point, whence the localization's maximal ideal is principal (`#469`).
  obtain ⟨a, b, hEq, rfl⟩ := exists_equation_and_eq_XYIdeal_of_isMaximal (W := W) p
  haveI : (XYIdeal W a (C b)).IsPrime := hp.isPrime
  have hns : W.Nonsingular a b := (W.equation_iff_nonsingular).mp hEq
  have hprin : (IsLocalRing.maximalIdeal (Localization.AtPrime (XYIdeal W a (C b)))).IsPrincipal :=
    maximalIdeal_isPrincipal_of_nonsingular W a b hns
  -- Principal maximal ideal of a Noetherian local domain ⇒ integrally closed (DVR TFAE).
  haveI : IsNoetherianRing (Localization.AtPrime (XYIdeal W a (C b))) :=
    IsLocalization.isNoetherianRing (XYIdeal W a (C b)).primeCompl _ inferInstance
  have htfae := tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
    (R := Localization.AtPrime (XYIdeal W a (C b)))
  exact ((htfae.out 4 3 rfl rfl).mp hprin).1

/-- **The coordinate ring of an elliptic curve over an algebraically closed field is a Dedekind
domain.** -/
theorem isDedekindDomain_of_isAlgClosed : IsDedekindDomain W.CoordinateRing :=
  have : IsIntegrallyClosed W.CoordinateRing := isIntegrallyClosed_of_isAlgClosed
  isDedekindDomain

end WeierstrassCurve.Affine.CoordinateRing
