/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByTwoPullback
import EllipticCurves.FunctionField.TranslationEndomorphism
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree

/-!
# The multiplication-by-`2` endomorphism of the function field

Let `W` be a Weierstrass curve over a field `F` of characteristic `≠ 2`, with affine coordinate ring
`F[W] = AdjoinRoot W.polynomial` and function field `F(W) = Frac F[W]`. Building on
`EllipticCurves/FunctionField/MulByTwoPullback.lean` — which constructs the *coordinate-ring half*
`mulByTwoCoordHom : F[W] →+* F(W)` of the multiplication-by-`2` pullback `[2]∗` — this file promotes
it to the full endomorphism of the function field:

* `WeierstrassCurve.Affine.CoordinateRing.mulByTwoEndo h₂ : F(W) →+* F(W)`.

The missing ingredient is that `mulByTwoCoordHom` is **injective** (the duplication map is
dominant), after which `IsFractionRing.lift` produces the endomorphism. This is the `[n]∗`
analogue (for `n = 2`) of the translation endomorphism `translateEndo`, and a substrate for a
divisor-theoretic
Weil pairing (`e_n(S, T)` involves the numerator `g_S ∘ [n]`).

## The dominance argument

Unlike translation — whose dominance follows from the group-law cancellation
`(P + T) + (-T) = P` — the multiplication-by-`2` map has no rational section, so dominance is proved
through the *degree* of the coordinate map instead:

* `transcendental_genX` (from `TranslationEndomorphism`): the generic `x`-coordinate
  `genX = x(P)` is transcendental over `F`.
* `genX_mem_algebraicClosure_of_mulByTwo`: if the image of the `x`-generator under `[2]∗` — the
  `x`-coordinate `Φ₂(genX)/Ψ₂Sq(genX)` of `2 • P` — is algebraic over `F`, then so is `genX`.
  Indeed, writing `u = Φ₂(genX)/Ψ₂Sq(genX)`, the generic `x`-coordinate is a root of the polynomial
  `Φ₂ − u·Ψ₂Sq` over the relative algebraic closure `K := algebraicClosure F F(W)`; this polynomial
  is nonzero because `Φ₂` has degree `4` (with leading coefficient `1`) while `Ψ₂Sq` has degree
  `≤ 3`, so its degree-`4` coefficient survives. Hence `genX` is algebraic over `K`, and as `K` is
  algebraic over `F`, `genX` is algebraic over `F`.
* If `mulByTwoCoordHom h₂` were not injective, its kernel would be a nonzero prime of the
  one-dimensional domain `F[W]` (Krull dimension `≤ 1` is `EllipticCurves.Torsion`'s
  `CoordinateRingDedekind`), hence maximal; by Zariski's lemma (`isAlgebraic_of_ker_maximal`, from
  `TranslationEndomorphism`) the residue field is algebraic over `F`, so the image `x(2 • P)` would
  be algebraic — forcing `genX` algebraic, contradicting `transcendental_genX`.

Notably the whole argument needs only `[Field F]` with `(2 : F) ≠ 0`; it does **not** invoke the
affine point group law, so — unlike `translateEndo` — it carries no `[W.IsElliptic]` hypothesis.

## Main definitions and statements

* `WeierstrassCurve.Affine.CoordinateRing.genX_mem_algebraicClosure_of_mulByTwo`.
* `WeierstrassCurve.Affine.CoordinateRing.mulByTwoCoordHom_injective`.
* `WeierstrassCurve.Affine.CoordinateRing.mulByTwoEndo`: the endomorphism `F(W) →+* F(W)`, with
  `mulByTwoEndo_algebraMap` (its value on `F[W]`) and the generator images `mulByTwoEndo_genX` and
  `mulByTwoEndo_genY`.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.6 (the duplication
  formula), III.8 (the Weil pairing).
-/

open Polynomial

namespace WeierstrassCurve.Affine
namespace CoordinateRing

open scoped Polynomial.Bivariate

variable {F : Type*} [Field F] {W : Affine F}

local notation "K" => algebraicClosure F W.FunctionField

/-- Evaluating a base-changed `F`-polynomial `p.map φ` at the generic `x`-coordinate equals the
`F`-algebra evaluation `aeval (genX W) p`. -/
private lemma eval_map_genX (p : F[X]) :
    (p.map (algebraMap F W.FunctionField)).eval (genX W) = aeval (genX W) p := by
  rw [eval_map, aeval_def]

/-- **`Ψ₂Sq` does not vanish at the generic `x`-coordinate.** It is the evaluation of the nonzero
`F`-polynomial `Ψ₂Sq` at the transcendental element `genX`. -/
private lemma Ψ₂Sq_eval_genX_ne (h4 : (4 : F) ≠ 0) :
    (W.map (algebraMap F W.FunctionField)).Ψ₂Sq.eval (genX W) ≠ 0 := by
  rw [map_Ψ₂Sq, eval_map_genX]
  intro h
  exact W.Ψ₂Sq_ne_zero h4 ((transcendental_iff.mp transcendental_genX) _ h)

/-- **Dominance of `[2]` (the `x`-coordinate side).** If the image of the `x`-generator under the
multiplication-by-`2` pullback — the `x`-coordinate `Φ₂(genX)/Ψ₂Sq(genX)` of `2 • P` — is algebraic
over `F`, then the generic `x`-coordinate `genX = x(P)` is algebraic over `F`. -/
lemma genX_mem_algebraicClosure_of_mulByTwo (h2 : (2 : F) ≠ 0)
    (hu : mulByTwoCoordHom h2 (mk W (C X)) ∈ K) :
    genX W ∈ K := by
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  rw [mulByTwoCoordHom_X] at hu
  set a := ((W.map (algebraMap F W.FunctionField)).Φ 2).eval (genX W) with ha
  set b := (W.map (algebraMap F W.FunctionField)).Ψ₂Sq.eval (genX W) with hb
  have hbne : b ≠ 0 := Ψ₂Sq_eval_genX_ne h4
  set u := a / b with hu_def
  have hub : u * b = a := by rw [hu_def]; exact div_mul_cancel₀ a hbne
  -- The witnessing polynomial `q = Φ₂ − u·Ψ₂Sq` over `K`.
  set uK : K := ⟨u, hu⟩ with huK_def
  set q : K[X] := (W.Φ 2).map (algebraMap F K) - C uK * (W.Ψ₂Sq).map (algebraMap F K) with hq
  -- `q ≠ 0`: its degree-`4` coefficient is `1` (from `Φ₂`), since `Ψ₂Sq` has degree `≤ 3`.
  have hΦ4 : ((W.Φ 2).map (algebraMap F K)).coeff 4 = 1 := by
    rw [coeff_map]
    have hc : (W.Φ 2).coeff 4 = 1 := W.coeff_Φ 2
    rw [hc, map_one]
  have hΨ4 : ((W.Ψ₂Sq).map (algebraMap F K)).coeff 4 = 0 := by
    have hlt : (W.Ψ₂Sq).natDegree < 4 :=
      lt_of_le_of_lt W.natDegree_Ψ₂Sq_le (by norm_num : (3 : ℕ) < 4)
    rw [coeff_map, coeff_eq_zero_of_natDegree_lt hlt, map_zero]
  have hq_ne : q ≠ 0 := by
    intro h0
    have hcoeff : q.coeff 4 = 0 := by rw [h0, coeff_zero]
    rw [hq, coeff_sub, coeff_C_mul, hΦ4, hΨ4, mul_zero, sub_zero] at hcoeff
    exact one_ne_zero hcoeff
  -- `aeval genX q = a − u·b = 0`.
  have hq_eval : (aeval (genX W)) q = 0 := by
    rw [hq, map_sub, map_mul, aeval_C, aeval_map_algebraMap, aeval_map_algebraMap,
      ← eval_map_genX, ← eval_map_genX, ← W.map_Φ, ← W.map_Ψ₂Sq]
    have huK : (algebraMap K W.FunctionField) uK = u := rfl
    rw [← ha, ← hb, huK, hub, sub_self]
  -- Conclude `genX` algebraic over `K`, hence over `F`.
  have halgK : IsAlgebraic K (genX W) := ⟨q, hq_ne, hq_eval⟩
  exact mem_algebraicClosure_iff.mpr (halgK.restrictScalars F)

/-- `mulByTwoCoordHom` is an `F`-algebra homomorphism: it fixes the image of `F`. -/
lemma mulByTwoCoordHom_algebraMap (h2 : (2 : F) ≠ 0) (c : F) :
    mulByTwoCoordHom h2 (algebraMap F W.CoordinateRing c) = algebraMap F W.FunctionField c := by
  have h1 : (algebraMap F W.CoordinateRing c) = mk W (C (C c)) := by
    rw [IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing, AdjoinRoot.algebraMap_eq,
      ← Polynomial.C_eq_algebraMap]; rfl
  rw [h1, show mk W (C (C c)) = AdjoinRoot.of W.polynomial (C c) from rfl, mulByTwoCoordHom,
    AdjoinRoot.lift_of, coe_eval₂RingHom, eval₂_C]

/-- `mulByTwoCoordHom` packaged as an `F`-algebra homomorphism. -/
noncomputable def mulByTwoAlgHom (h2 : (2 : F) ≠ 0) :
    W.CoordinateRing →ₐ[F] W.FunctionField where
  toRingHom := mulByTwoCoordHom h2
  commutes' := mulByTwoCoordHom_algebraMap h2

@[simp] lemma mulByTwoAlgHom_apply (h2 : (2 : F) ≠ 0) (a : W.CoordinateRing) :
    mulByTwoAlgHom h2 a = mulByTwoCoordHom h2 a := rfl

set_option maxHeartbeats 400000 in
-- Elaborating the Zariski step specialises `isAlgebraic_of_ker_maximal` to `F[W]` and unfolds the
-- large `AdjoinRoot.lift` term behind `mulByTwoCoordHom`; this defeq check needs a little over the
-- default heartbeat budget.
/-- **Multiplication by `2` is dominant: `mulByTwoCoordHom h₂` is injective.** If it were not, its
kernel would be a nonzero prime — hence maximal, as `F[W]` has Krull dimension `≤ 1` — so the
residue field would be algebraic over `F` (Zariski), forcing the generic `x`-coordinate to be
algebraic and contradicting `transcendental_genX`. -/
lemma mulByTwoCoordHom_injective (h2 : (2 : F) ≠ 0) :
    Function.Injective (mulByTwoCoordHom (W := W) h2) := by
  set g := mulByTwoAlgHom (W := W) h2 with hg_def
  have key : Function.Injective g := by
    by_contra hni
    have hne : RingHom.ker g ≠ ⊥ := fun h =>
      hni ((RingHom.injective_iff_ker_eq_bot _).mpr h)
    haveI hprime : (RingHom.ker g).IsPrime := RingHom.ker_isPrime _
    have hmax : (RingHom.ker g).IsMaximal := hprime.isMaximal hne
    have hu : IsAlgebraic F (g (mk W (C X))) :=
      isAlgebraic_of_ker_maximal g hmax (mk W (C X))
    rw [hg_def, mulByTwoAlgHom_apply] at hu
    have hgen : genX W ∈ K :=
      genX_mem_algebraicClosure_of_mulByTwo h2 (mem_algebraicClosure_iff.mpr hu)
    exact transcendental_genX (mem_algebraicClosure_iff.mp hgen)
  exact key

/-- **The multiplication-by-`2` endomorphism of the function field.** The ring endomorphism
`F(W) →+* F(W)` realising `h ↦ h ∘ [2]`, obtained from the injective coordinate-ring pullback
`mulByTwoCoordHom h₂` by the universal property of the fraction field. -/
noncomputable def mulByTwoEndo (h2 : (2 : F) ≠ 0) :
    W.FunctionField →+* W.FunctionField :=
  IsFractionRing.lift (mulByTwoCoordHom_injective h2)

/-- On the image of `F[W]`, `mulByTwoEndo` agrees with the coordinate-ring pullback. -/
@[simp] lemma mulByTwoEndo_algebraMap (h2 : (2 : F) ≠ 0) (a : W.CoordinateRing) :
    mulByTwoEndo h2 (algebraMap W.CoordinateRing W.FunctionField a) = mulByTwoCoordHom h2 a :=
  IsFractionRing.lift_algebraMap (mulByTwoCoordHom_injective h2) a

/-- The image of the generic `x`-coordinate: the `x`-coordinate of `2 • P`. -/
lemma mulByTwoEndo_genX (h2 : (2 : F) ≠ 0) :
    mulByTwoEndo h2 (genX W) =
      ((W.map (algebraMap F W.FunctionField)).Φ 2).eval (genX W) /
        (W.map (algebraMap F W.FunctionField)).Ψ₂Sq.eval (genX W) := by
  conv_lhs => rw [genX, genPsi]
  rw [mulByTwoEndo_algebraMap, mulByTwoCoordHom_X]

/-- The image of the generic `y`-coordinate: the `y`-coordinate of `2 • P`. -/
lemma mulByTwoEndo_genY (h2 : (2 : F) ≠ 0) :
    mulByTwoEndo h2 (genY W) =
      (((W.map (algebraMap F W.FunctionField)).preΨ₄.eval (genX W) -
          ((W.map (algebraMap F W.FunctionField)).ψ 2).evalEval (genX W) (genY W) *
            ((W.map (algebraMap F W.FunctionField)).a₁ *
                ((W.map (algebraMap F W.FunctionField)).Φ 2).eval (genX W) +
              (W.map (algebraMap F W.FunctionField)).a₃ *
                (W.map (algebraMap F W.FunctionField)).Ψ₂Sq.eval (genX W))) /
        (2 * ((W.map (algebraMap F W.FunctionField)).ψ 2).evalEval (genX W) (genY W) ^ 3)) := by
  conv_lhs => rw [genY]
  rw [mulByTwoEndo_algebraMap, mulByTwoCoordHom_root]

end CoordinateRing
end WeierstrassCurve.Affine
