/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import EllipticCurves.FunctionField.CoordinateRingNormalGeneral
import EllipticCurves.FunctionField.MulByNYCoordFormula
import EllipticCurves.Torsion.CoprimeAdjacent
import EllipticCurves.Torsion.OmegaChordSum
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Unramified.Locus

/-!
# Multiplication by `n` on affine coordinate rings: `F[W] → F[W][1/ψₙ]` is finite étale

Let `W` be an elliptic curve over a field `F`, `F[W]` its affine coordinate ring (the functions on
`E ∖ {O}`), `n` an index with `(2 : F) ≠ 0` and `(n : F) ≠ 0` (both as `NeZero` instances),
`ψₙ ∈ F[W]` the `n`-division polynomial (`psiN`) and `Bₙ = F[W][1/ψₙ]` (`AwayPsiN`, the functions
on `E ∖ E[n]`).  The formulae

  `x ↦ Φₙ(x)/ψₙ²`, `y ↦ (εₙ preΩₙ(x) - ψₙ (a₁ Φₙ(x) + a₃ ΨSqₙ(x))) / (2 ψₙ³)`

(`εₙ = 1` for even `n` and `εₙ = ψ₂` for odd `n`, the parity factor of `omegaY`) define the
`F`-algebra map `mulByNAlgHom : F[W] →ₐ[F] Bₙ`.  Inside `F(W)` it is the multiplication-by-`n`
pullback built from the group law (`algebraMap_mulByNRingHom`, `comp_mulByNRingHom`): composed
with the inclusion `Bₙ ⊆ F(W)` it is `mulByNCoordHom`, i.e. `mulByNEndo` on `F[W] ⊆ F(W)`.

`MulByNCover W n` is a type synonym for `Bₙ` carrying the `F[W]`-algebra structure given by
`mulByNAlgHom`.  For it:

* `Module.Finite W.CoordinateRing (MulByNCover W n)`: `x` is a root of the monic
  `Φₙ(T) - [n]∗x · ΨSqₙ(T)`, `y` is integral since `ψ₂² = Ψ₂Sq(x)`, and
  `1/ψₙ² = u(x) [n]∗x + v(x)` for a Bézout identity `u Φₙ + v ΨSqₙ = 1` (`isCoprime_Φ_ΨSq`).
* `Algebra.FormallyUnramified`: `Bₙ` carries the derivation `δ` (`deltaN`) with `δ x = ψ₂`,
  `δ y = -W_X`, every `F`-derivation is `d b = δ(b) · ω` with `ω = c dx - e dy` for
  `c ψ₂ + e W_X = 1`, and the Wronskian identity `hasWronskianId` gives `[n]∗ω = n ω`.  As `n` is
  invertible, `ω` vanishes in `Ω[Bₙ⁄F[W]]`.
* `Module.Flat`: `F[W]` is a Dedekind domain and `Bₙ` is a torsion-free domain.
* `Algebra.Etale W.CoordinateRing (MulByNCover W n)`.

This is the commutative-algebra content of `CurvesJacobian.Cusp.EllipticMulByN` of
`curves-jacobian`, ported with the scheme layer removed and with `CharZero` weakened to the two
`NeZero` hypotheses.
-/

open Polynomial
open scoped Polynomial.Bivariate DualNumber

namespace WeierstrassCurve.Affine.CoordinateRing

variable {F : Type*} [Field F] (W : Affine F) (n : ℕ)

section Basic

local notation "A" => W.CoordinateRing

/-- The coordinate `x` of `F[W]`. -/
noncomputable abbrev coordX : A := mk W (C X)

/-- The coordinate `y` of `F[W]`. -/
noncomputable abbrev coordY : A := AdjoinRoot.root W.polynomial

/-- `ψ₂ = 2y + a₁x + a₃ = W_Y` in `F[W]`. -/
noncomputable def coordψ₂ : A := mk W W.polynomialY

/-- `W_X = a₁ y - (3x² + 2a₂ x + a₄)` in `F[W]`. -/
noncomputable def coordWX : A :=
  algebraMap F A W.a₁ * coordY W -
    (3 * coordX W ^ 2 + algebraMap F A (2 * W.a₂) * coordX W + algebraMap F A W.a₄)

/-- The `n`-division polynomial `ψₙ` in `F[W]`. -/
noncomputable def psiN : A := mk W (W.ψ n)

/-- `F[W][1/ψₙ]`, the ring of functions on `E ∖ E[n]`, with its localisation algebra structure. -/
abbrev AwayPsiN := Localization.Away (psiN W n)

lemma coordψ₂_eq : coordψ₂ W = 2 * coordY W + algebraMap F A W.a₁ * coordX W +
    algebraMap F A W.a₃ := by
  change coordψ₂ W = 2 * AdjoinRoot.root W.polynomial +
      AdjoinRoot.of _ (C W.a₁) * AdjoinRoot.mk W.polynomial (C X) + AdjoinRoot.of _ (C W.a₃)
  rw [coordψ₂, polynomialY, ← AdjoinRoot.mk_X, ← AdjoinRoot.mk_C, ← AdjoinRoot.mk_C,
    ← map_ofNat (AdjoinRoot.mk W.polynomial), ← map_mul, ← map_mul, ← map_add, ← map_add]
  congr 1
  simp only [map_ofNat, C_add, C_mul]
  ring

lemma coordψ₂_sq : coordψ₂ W ^ 2 = algebraMap F[X] A W.Ψ₂Sq := by
  rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C]
  exact mk_ψ₂_sq (W := W)

lemma algebraMap_polynomial_injective : Function.Injective (algebraMap F[X] A) := by
  refine (injective_iff_map_eq_zero _).2 fun p hp ↦ ?_
  have h : p • (1 : A) + (0 : F[X]) • mk W Y = 0 := by
    rw [zero_smul, add_zero, Algebra.smul_def, mul_one, hp]
  exact (smul_basis_eq_zero h).1

/-- `ψ₂ = (a₁X + a₃) • 1 + 2 • Y` in terms of the basis `1, Y` of `F[W]` over `F[X]`. -/
lemma coordψ₂_eq_smul : coordψ₂ W = (C W.a₁ * X + C W.a₃) • (1 : A) +
    (C 2 : F[X]) • mk W Y := by
  rw [Algebra.smul_def, Algebra.smul_def, AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C,
    ← AdjoinRoot.mk_C, mul_one, ← map_mul, ← map_add, coordψ₂, polynomialY]
  congr 1
  ring

lemma coordψ₂_ne_zero [NeZero (2 : F)] : coordψ₂ W ≠ 0 := by
  intro h
  rw [coordψ₂_eq_smul] at h
  have h2 := (smul_basis_eq_zero h).2
  rw [C_eq_zero] at h2
  exact two_ne_zero h2

/-- The Weierstrass equation in `F[W]`. -/
lemma coord_equation : coordY W ^ 2 + algebraMap F A W.a₁ * coordX W * coordY W +
    algebraMap F A W.a₃ * coordY W - (coordX W ^ 3 + algebraMap F A W.a₂ * coordX W ^ 2 +
      algebraMap F A W.a₄ * coordX W + algebraMap F A W.a₆) = 0 := by
  apply IsFractionRing.injective A W.FunctionField
  have h := equation_gen (W := W)
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at h
  simp only [map_sub, map_add, map_mul, map_pow, map_zero, ← IsScalarTower.algebraMap_apply]
  change genY W ^ 2 + _ * genX W * genY W + _ * genY W -
    (genX W ^ 3 + _ * genX W ^ 2 + _ * genX W + _) = 0
  linear_combination h

/-- **Nonsingularity**: `ψ₂` and `W_X` generate the unit ideal of `F[W]`. -/
theorem exists_mul_coordψ₂_add_mul_coordWX [W.IsElliptic] :
    ∃ c d : A, c * coordψ₂ W + d * coordWX W = 1 := by
  by_contra hne
  have hI : Ideal.span {coordψ₂ W, coordWX W} ≠ ⊤ := by
    intro h
    obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.1 (h ▸ Submodule.mem_top (x := (1 : A)))
    exact hne ⟨c, d, hcd⟩
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal _ hI
  letI := Ideal.Quotient.field m
  let π : A →ₐ[F] A ⧸ m := Ideal.Quotient.mkₐ F m
  have hψ : π (coordψ₂ W) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (hIm (Ideal.subset_span (by simp)))
  have hw : π (coordWX W) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (hIm (Ideal.subset_span (by simp)))
  have heq : (W.map (algebraMap F (A ⧸ m))).toAffine.Equation (π (coordX W)) (π (coordY W)) := by
    rw [WeierstrassCurve.Affine.equation_iff]
    have := congrArg π (coord_equation W)
    simp only [map_sub, map_add, map_mul, map_pow, AlgHom.commutes, map_zero] at this
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
    linear_combination this
  have hns := (WeierstrassCurve.Affine.equation_iff_nonsingular.1 heq)
  rw [WeierstrassCurve.Affine.nonsingular_iff'] at hns
  rcases hns.2 with h | h
  · apply h
    rw [coordWX] at hw
    simp only [map_sub, map_add, map_mul, map_pow, AlgHom.commutes, map_ofNat] at hw
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄]
    linear_combination hw
  · apply h
    rw [coordψ₂_eq] at hψ
    simp only [map_add, map_mul, AlgHom.commutes, map_ofNat] at hψ
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
    linear_combination hψ

lemma psiN_two : psiN W 2 = coordψ₂ W := by
  rw [psiN, Nat.cast_ofNat, WeierstrassCurve.ψ_two]
  rfl

lemma psiN_sq : psiN W n ^ 2 = algebraMap F[X] A (W.ΨSq n) := by
  rw [psiN, mk_ψ, mk_Ψ_sq]
  rfl

lemma psiN_eq : psiN W n =
    algebraMap F[X] A (W.preΨ n) * (if Even (n : ℤ) then coordψ₂ W else 1) := by
  rw [psiN, mk_ψ, WeierstrassCurve.Ψ, map_mul, apply_ite (AdjoinRoot.mk _), map_one]
  rfl

/-- `εₙ = 1` for even `n` and `εₙ = ψ₂` for odd `n`, so that `preΨₙ ψ₂ = εₙ ψₙ`. -/
noncomputable def epsN : A := if Even (n : ℤ) then 1 else coordψ₂ W

lemma preΨ_mul_coordψ₂ : algebraMap F[X] A (W.preΨ n) * coordψ₂ W = epsN W n * psiN W n := by
  rw [psiN_eq, epsN]
  split_ifs <;> ring

lemma algebraMap_polynomial_eq_aeval_coordX (p : F[X]) :
    algebraMap F[X] A p = aeval (coordX W) p := by
  rw [show coordX W = algebraMap F[X] A X from rfl, aeval_algebraMap_apply, aeval_X_left_apply]

lemma intCast_ne_zero_of_neZero [NeZero (n : F)] : ((n : ℤ) : F) ≠ 0 := by
  rw [Int.cast_natCast]
  exact NeZero.ne _

lemma ne_zero_of_neZero_cast [NeZero (n : F)] : n ≠ 0 := by
  rintro rfl
  exact NeZero.ne ((0 : ℕ) : F) Nat.cast_zero

lemma psiN_ne_zero [NeZero (n : F)] : psiN W n ≠ 0 := by
  intro h
  have h2 := psiN_sq W n
  rw [h, zero_pow two_ne_zero] at h2
  exact W.ΨSq_ne_zero (intCast_ne_zero_of_neZero n)
    ((map_eq_zero_iff _ (algebraMap_polynomial_injective W)).1 h2.symm)

end Basic

/-! ### The type synonym and the derivation `δ` -/

section Delta

local notation "A" => W.CoordinateRing

/-- `F[W][1/ψₙ]`, to be regarded as an `F[W]`-algebra through the multiplication-by-`n` map
`mulByNAlgHom` rather than through localisation. -/
def MulByNCover : Type _ := AwayPsiN W n

noncomputable instance : CommRing (MulByNCover W n) := inferInstanceAs (CommRing (AwayPsiN W n))

noncomputable instance : Algebra F (MulByNCover W n) :=
  inferInstanceAs (Algebra F (AwayPsiN W n))

/-- The identity `AwayPsiN W n → MulByNCover W n`. -/
noncomputable def toMulByNCover : AwayPsiN W n ≃ₐ[F] MulByNCover W n := AlgEquiv.refl

/-- The localisation map `F[W] → MulByNCover W n` (not the algebra map of `MulByNCover W n`). -/
noncomputable def locN : A →ₐ[F] MulByNCover W n :=
  (toMulByNCover W n).toAlgHom.comp (IsScalarTower.toAlgHom F A (AwayPsiN W n))

lemma locN_apply (a : A) : locN W n a = toMulByNCover W n (algebraMap A (AwayPsiN W n) a) := rfl

/-- `1/ψₙ` in `MulByNCover W n`. -/
noncomputable abbrev invPsiNM : MulByNCover W n :=
  toMulByNCover W n (IsLocalization.Away.invSelf (psiN W n))

lemma locN_psiN_mul_invPsiNM : locN W n (psiN W n) * invPsiNM W n = 1 := by
  rw [locN_apply, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]

lemma locN_mem_adjoin (a : A) :
    locN W n a ∈ Algebra.adjoin F {locN W n (coordX W), locN W n (coordY W)} := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  induction p using Polynomial.induction_on with
  | C q =>
    rw [show AdjoinRoot.mk W.polynomial (C q) = algebraMap F[X] A q from rfl,
      algebraMap_polynomial_eq_aeval_coordX, ← aeval_algHom_apply]
    exact Algebra.adjoin_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _))
      (q.aeval_mem_adjoin_singleton F (locN W n (coordX W)))
  | add p q hp hq => rw [map_add, map_add]; exact add_mem hp hq
  | monomial k q h =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul]
    exact mul_mem h (Algebra.subset_adjoin (Set.mem_insert_of_mem _
      (Set.mem_singleton_iff.2 (by rw [AdjoinRoot.mk_X]))))

lemma adjoin_eq_top_mulByNCover :
    Algebra.adjoin F {locN W n (coordX W), locN W n (coordY W), invPsiNM W n} = ⊤ := by
  refine eq_top_iff.2 fun b _ ↦ ?_
  obtain ⟨k, a, h⟩ := IsLocalization.Away.surj (psiN W n) ((toMulByNCover W n).symm b)
  have hb : b = locN W n a * invPsiNM W n ^ k := by
    rw [locN_apply, ← map_pow, ← map_mul, ← h, mul_assoc, ← mul_pow,
      IsLocalization.Away.mul_invSelf, one_pow, mul_one, AlgEquiv.apply_symm_apply]
  rw [hb]
  refine mul_mem (Algebra.adjoin_mono ?_ (locN_mem_adjoin W n a))
    (pow_mem (Algebra.subset_adjoin (by simp)) k)
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
  tauto

omit W n in
/-- The Weierstrass equation, first-order deformed: if `(x, y)` lies on the curve and
`W_X a + W_Y b = 0`, then `(x + aε, y + bε)` lies on the curve over the dual numbers. -/
lemma weierstrass_dual {R : Type*} [CommRing R] (a₁ a₂ a₃ a₄ a₆ x y a b : R)
    (h : y ^ 2 + a₁ * x * y + a₃ * y - (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) = 0)
    (hd : (a₁ * y - (3 * x ^ 2 + 2 * a₂ * x + a₄)) * a + (2 * y + a₁ * x + a₃) * b = 0) :
    (algebraMap R R[ε] y + algebraMap R R[ε] b * ε) ^ 2 +
      algebraMap R R[ε] a₁ * (algebraMap R R[ε] x + algebraMap R R[ε] a * ε) *
        (algebraMap R R[ε] y + algebraMap R R[ε] b * ε) +
      algebraMap R R[ε] a₃ * (algebraMap R R[ε] y + algebraMap R R[ε] b * ε) -
      ((algebraMap R R[ε] x + algebraMap R R[ε] a * ε) ^ 3 +
        algebraMap R R[ε] a₂ * (algebraMap R R[ε] x + algebraMap R R[ε] a * ε) ^ 2 +
        algebraMap R R[ε] a₄ * (algebraMap R R[ε] x + algebraMap R R[ε] a * ε) +
        algebraMap R R[ε] a₆) = 0 := by
  have h' := congrArg (algebraMap R R[ε]) h
  have hd' := congrArg (algebraMap R R[ε]) hd
  simp only [map_add, map_sub, map_mul, map_pow, map_zero, map_ofNat] at h' hd'
  set i := algebraMap R R[ε]
  linear_combination h' + (ε : R[ε]) * hd' + (i b ^ 2 + i a₁ * i a * i b - 3 * i x * i a ^ 2 -
    i a₂ * i a ^ 2 - i a ^ 3 * ε) * DualNumber.eps_mul_eps (R := R)

local notation "M" => MulByNCover W n

lemma locN_equation : locN W n (coordY W) ^ 2 + algebraMap F M W.a₁ * locN W n (coordX W) *
    locN W n (coordY W) + algebraMap F M W.a₃ * locN W n (coordY W) -
      (locN W n (coordX W) ^ 3 + algebraMap F M W.a₂ * locN W n (coordX W) ^ 2 +
        algebraMap F M W.a₄ * locN W n (coordX W) + algebraMap F M W.a₆) = 0 := by
  have h := congrArg (locN W n) (coord_equation W)
  simpa only [map_sub, map_add, map_mul, map_pow, AlgHom.commutes, map_zero] using h

lemma locN_coordψ₂ : locN W n (coordψ₂ W) = 2 * locN W n (coordY W) +
    algebraMap F M W.a₁ * locN W n (coordX W) + algebraMap F M W.a₃ := by
  rw [coordψ₂_eq]
  simp only [map_add, map_mul, AlgHom.commutes, map_ofNat]

lemma locN_coordWX : locN W n (coordWX W) = algebraMap F M W.a₁ * locN W n (coordY W) -
    (3 * locN W n (coordX W) ^ 2 + 2 * algebraMap F M W.a₂ * locN W n (coordX W) +
      algebraMap F M W.a₄) := by
  rw [coordWX]
  simp only [map_sub, map_add, map_mul, map_pow, AlgHom.commutes, map_ofNat]

/-- `F[W] → M[ε]`, `x ↦ x + ψ₂ ε`, `y ↦ y - W_X ε`: the tangent vector field dual to the invariant
differential. -/
noncomputable def deltaHomA : A →+* M[ε] :=
  AdjoinRoot.lift (eval₂RingHom ((algebraMap M M[ε]).comp (algebraMap F M))
    (algebraMap M M[ε] (locN W n (coordX W)) + algebraMap M M[ε] (locN W n (coordψ₂ W)) * ε))
    (algebraMap M M[ε] (locN W n (coordY W)) + algebraMap M M[ε] (-locN W n (coordWX W)) * ε) (by
      have hd : (algebraMap F M W.a₁ * locN W n (coordY W) - (3 * locN W n (coordX W) ^ 2 +
          2 * algebraMap F M W.a₂ * locN W n (coordX W) + algebraMap F M W.a₄)) *
          locN W n (coordψ₂ W) + (2 * locN W n (coordY W) + algebraMap F M W.a₁ *
            locN W n (coordX W) + algebraMap F M W.a₃) * (-locN W n (coordWX W)) = 0 := by
        rw [locN_coordψ₂, locN_coordWX]; ring
      have key := weierstrass_dual _ _ _ _ _ _ _ _ _ (locN_equation W n) hd
      rw [eval₂_eval₂RingHom_apply, ← WeierstrassCurve.Affine.map_polynomial]
      change (W.map ((algebraMap M M[ε]).comp (algebraMap F M))).toAffine.Equation _ _
      rw [WeierstrassCurve.Affine.equation_iff]
      simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
        WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, RingHom.comp_apply]
      linear_combination key)

lemma deltaHomA_algebraMap (c : F) :
    deltaHomA W n (algebraMap F A c) = algebraMap M M[ε] (algebraMap F M c) := by
  rw [IsScalarTower.algebraMap_apply F F[X] A, AdjoinRoot.algebraMap_eq, deltaHomA,
    AdjoinRoot.lift_of, coe_eval₂RingHom, Polynomial.algebraMap_apply, eval₂_C]
  rfl

lemma deltaHomA_coordX : deltaHomA W n (coordX W) =
    algebraMap M M[ε] (locN W n (coordX W)) + algebraMap M M[ε] (locN W n (coordψ₂ W)) * ε := by
  have h : coordX W = AdjoinRoot.of W.polynomial X := rfl
  rw [h, deltaHomA, AdjoinRoot.lift_of, coe_eval₂RingHom, eval₂_X]
  rfl

lemma deltaHomA_coordY : deltaHomA W n (coordY W) =
    algebraMap M M[ε] (locN W n (coordY W)) + algebraMap M M[ε] (-locN W n (coordWX W)) * ε := by
  rw [deltaHomA, AdjoinRoot.lift_root]

lemma fst_comp_deltaHomA :
    (TrivSqZeroExt.fstHom F M M).toRingHom.comp (deltaHomA W n) = (locN W n).toRingHom := by
  refine AdjoinRoot.ringHom_ext ?_ ?_
  · refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
    · change (deltaHomA W n (algebraMap F A c)).fst = locN W n (algebraMap F A c)
      rw [deltaHomA_algebraMap, AlgHom.commutes, TrivSqZeroExt.algebraMap_eq_inl,
        TrivSqZeroExt.fst_inl]
    · change (deltaHomA W n (coordX W)).fst = locN W n (coordX W)
      rw [deltaHomA_coordX]
      simp [TrivSqZeroExt.algebraMap_eq_inl]
  · change (deltaHomA W n (coordY W)).fst = locN W n (coordY W)
    rw [deltaHomA_coordY]
    simp [TrivSqZeroExt.algebraMap_eq_inl]

lemma fst_deltaHomA (a : A) : (deltaHomA W n a).fst = locN W n a :=
  RingHom.congr_fun (fst_comp_deltaHomA W n) a

lemma isUnit_deltaHomA_psiN : IsUnit (deltaHomA W n (psiN W n)) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, fst_deltaHomA]
  exact IsUnit.of_mul_eq_one _ (locN_psiN_mul_invPsiNM W n)

/-- The extension of `deltaHomA` to the localisation. -/
noncomputable def deltaHom : AwayPsiN W n →+* M[ε] :=
  IsLocalization.Away.lift (psiN W n) (isUnit_deltaHomA_psiN W n)

lemma deltaHom_algebraMap (a : A) :
    deltaHom W n (algebraMap A (AwayPsiN W n) a) = deltaHomA W n a :=
  IsLocalization.Away.lift_eq _ _ a

lemma fst_deltaHom (b : AwayPsiN W n) : (deltaHom W n b).fst = toMulByNCover W n b := by
  have h : (TrivSqZeroExt.fstHom F M M).toRingHom.comp (deltaHom W n) =
      (toMulByNCover W n).toRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (psiN W n)) ?_
    rw [RingHom.comp_assoc, deltaHom, IsLocalization.Away.lift_comp, fst_comp_deltaHomA]
    rfl
  exact RingHom.congr_fun h b

/-- The additive map underlying `δ`. -/
noncomputable def deltaLin : M →ₗ[F] M where
  toFun b := (deltaHom W n ((toMulByNCover W n).symm b)).snd
  map_add' a b := by rw [map_add, map_add, TrivSqZeroExt.snd_add]
  map_smul' c b := by
    rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, map_mul,
      IsScalarTower.algebraMap_apply F A (AwayPsiN W n), deltaHom_algebraMap,
      deltaHomA_algebraMap, DualNumber.snd_mul]
    simp [TrivSqZeroExt.algebraMap_eq_inl, Algebra.smul_def]

/-- **The derivation `δ` of `F[W][1/ψₙ]`** with `δ x = ψ₂`, `δ y = -W_X`, so that `d b = δ(b) · ω`
for the invariant differential `ω = dx/ψ₂`. -/
noncomputable def deltaN : Derivation F M M :=
  Derivation.mk' (deltaLin W n) fun a b ↦ by
    change (deltaHom W n ((toMulByNCover W n).symm (a * b))).snd =
      a * (deltaHom W n ((toMulByNCover W n).symm b)).snd +
        b * (deltaHom W n ((toMulByNCover W n).symm a)).snd
    rw [map_mul, map_mul, DualNumber.snd_mul, fst_deltaHom, fst_deltaHom]
    simp only [AlgEquiv.apply_symm_apply]
    ring

lemma deltaN_locN (a : A) : deltaN W n (locN W n a) = (deltaHomA W n a).snd := by
  have h : (toMulByNCover W n).symm (locN W n a) = algebraMap A (AwayPsiN W n) a := by
    rw [locN_apply, AlgEquiv.symm_apply_apply]
  change (deltaHom W n ((toMulByNCover W n).symm (locN W n a))).snd = _
  rw [h, deltaHom_algebraMap]

lemma deltaN_coordX : deltaN W n (locN W n (coordX W)) = locN W n (coordψ₂ W) := by
  rw [deltaN_locN, deltaHomA_coordX]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

lemma deltaN_coordY : deltaN W n (locN W n (coordY W)) = -locN W n (coordWX W) := by
  rw [deltaN_locN, deltaHomA_coordY]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

/-- Every `F`-derivation `d` of `M` is `d b = δ(b) • ω` with `ω = c dx - e dy`. -/
lemma derivation_eq_deltaN_smul {P : Type*} [AddCommGroup P] [Module M P] [Module F P]
    [IsScalarTower F M P] (d : Derivation F M P) {c e : A}
    (hce : c * coordψ₂ W + e * coordWX W = 1) (b : M) : d b = deltaN W n b •
      (locN W n c • d (locN W n (coordX W)) - locN W n e • d (locN W n (coordY W))) := by
  have heq0 : locN W n (coordY W) * locN W n (coordY W) + algebraMap F M W.a₁ *
      locN W n (coordX W) * locN W n (coordY W) + algebraMap F M W.a₃ * locN W n (coordY W) -
      (locN W n (coordX W) * locN W n (coordX W) * locN W n (coordX W) + algebraMap F M W.a₂ *
        locN W n (coordX W) * locN W n (coordX W) + algebraMap F M W.a₄ * locN W n (coordX W) +
        algebraMap F M W.a₆) = 0 := by
    linear_combination locN_equation W n
  have hrel : locN W n (coordWX W) • d (locN W n (coordX W)) + locN W n (coordψ₂ W) •
      d (locN W n (coordY W)) = 0 := by
    have h := congrArg d heq0
    simp only [map_sub, map_add, Derivation.leibniz, Derivation.map_algebraMap, smul_zero,
      map_zero] at h
    rw [locN_coordψ₂, locN_coordWX]
    linear_combination (norm := module) h
  have hce' := congrArg (locN W n) hce
  simp only [map_add, map_mul, map_one] at hce'
  let d' : Derivation F M P := (LinearMap.toSpanSingleton M P
    (locN W n c • d (locN W n (coordX W)) - locN W n e • d (locN W n (coordY W)))).compDer
      (deltaN W n)
  have hd' : ∀ z, d' z = deltaN W n z •
      (locN W n c • d (locN W n (coordX W)) - locN W n e • d (locN W n (coordY W))) :=
    fun z ↦ rfl
  have hx : d (locN W n (coordX W)) = d' (locN W n (coordX W)) := by
    rw [hd', deltaN_coordX]
    linear_combination (norm := module) (locN W n e) • hrel - hce' • d (locN W n (coordX W))
  have hy : d (locN W n (coordY W)) = d' (locN W n (coordY W)) := by
    rw [hd', deltaN_coordY]
    linear_combination (norm := module) (locN W n c) • hrel - hce' • d (locN W n (coordY W))
  have hxy : Set.EqOn d d' {locN W n (coordX W), locN W n (coordY W)} := by
    intro z hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hu : d (invPsiNM W n) = d' (invPsiNM W n) := by
    have h1 : invPsiNM W n * locN W n (psiN W n) = 1 := by
      rw [mul_comm]; exact locN_psiN_mul_invPsiNM W n
    rw [Derivation.leibniz_of_mul_eq_one d h1, Derivation.leibniz_of_mul_eq_one d' h1,
      Derivation.eqOn_adjoin hxy (locN_mem_adjoin W n (psiN W n))]
  have heq : d = d' := by
    refine Derivation.ext_of_adjoin_eq_top _ (adjoin_eq_top_mulByNCover W n) ?_
    intro z hz
    rcases hz with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hu
  calc d b = d' b := by rw [heq]
    _ = _ := hd' b

end Delta

/-! ### Elements of `F[W][1/ψₙ]` and the coordinates of `n • 𝒫` -/

section Coords

local notation "A" => W.CoordinateRing

/-- `x ∈ F[W][1/ψₙ]`. -/
noncomputable abbrev xAway : AwayPsiN W n := algebraMap A (AwayPsiN W n) (coordX W)

/-- `ψₙ ∈ F[W][1/ψₙ]`. -/
noncomputable abbrev psiNAway : AwayPsiN W n := algebraMap A (AwayPsiN W n) (psiN W n)

/-- `1/ψₙ ∈ F[W][1/ψₙ]`. -/
noncomputable abbrev invPsiNAway : AwayPsiN W n := IsLocalization.Away.invSelf (psiN W n)

lemma psiNAway_mul_invPsiNAway : psiNAway W n * invPsiNAway W n = 1 :=
  IsLocalization.Away.mul_invSelf _

lemma algebraMap_aeval_coordX (p : F[X]) :
    algebraMap A (AwayPsiN W n) (aeval (coordX W) p) = aeval (xAway W n) p :=
  (aeval_algHom_apply (IsScalarTower.toAlgHom F A (AwayPsiN W n)) (coordX W) p).symm

lemma psiNAway_sq : psiNAway W n ^ 2 = aeval (xAway W n) (W.ΨSq n) := by
  rw [← map_pow, psiN_sq, algebraMap_polynomial_eq_aeval_coordX, algebraMap_aeval_coordX]

/-- The `x`-coordinate of `n • 𝒫`, `Φₙ(x)/ψₙ²`. -/
noncomputable def xNAway : AwayPsiN W n := aeval (xAway W n) (W.Φ n) * invPsiNAway W n ^ 2

/-- The `y`-coordinate of `n • 𝒫`, `(εₙ preΩₙ(x) - ψₙ (a₁ Φₙ(x) + a₃ ΨSqₙ(x))) / (2 ψₙ³)`, where
`εₙ = 1` for even `n` and `εₙ = ψ₂` for odd `n` (the parity factor of `omegaY`). -/
noncomputable def yNAway : AwayPsiN W n :=
  algebraMap F (AwayPsiN W n) 2⁻¹ * (algebraMap A (AwayPsiN W n) (epsN W n) *
    aeval (xAway W n) (W.preΩ n) - psiNAway W n * (algebraMap F (AwayPsiN W n) W.a₁ *
      aeval (xAway W n) (W.Φ n) + algebraMap F (AwayPsiN W n) W.a₃ *
        aeval (xAway W n) (W.ΨSq n))) * invPsiNAway W n ^ 3

lemma xNAway_mul_psiNAway_sq : xNAway W n * psiNAway W n ^ 2 = aeval (xAway W n) (W.Φ n) := by
  rw [xNAway]
  linear_combination aeval (xAway W n) (W.Φ n) * (psiNAway W n * invPsiNAway W n + 1) *
    psiNAway_mul_invPsiNAway W n

/-- `1/ψₙ² = u(x) x(n • 𝒫) + v(x)` for a Bézout identity `u Φₙ + v ΨSqₙ = 1`. -/
lemma exists_invPsiNAway_sq [NeZero (2 : F)] [W.IsElliptic] :
    ∃ a b : F[X], invPsiNAway W n ^ 2 = aeval (xAway W n) a * xNAway W n +
      aeval (xAway W n) b := by
  obtain ⟨a, b, hab⟩ := isCoprime_Φ_ΨSq (W := W) two_ne_zero (n : ℤ)
  have hab' : a * W.Φ n + b * W.ΨSq n = 1 := hab
  refine ⟨a, b, ?_⟩
  have h := congrArg (aeval (xAway W n)) hab'
  rw [map_add, map_mul, map_mul, map_one, ← xNAway_mul_psiNAway_sq, ← psiNAway_sq] at h
  linear_combination (-(invPsiNAway W n ^ 2)) * h + (aeval (xAway W n) a * xNAway W n +
    aeval (xAway W n) b) * (psiNAway W n * invPsiNAway W n + 1) * psiNAway_mul_invPsiNAway W n

end Coords

/-! ### `F[W][1/ψₙ]` inside the function field, and the map `[n]∗` -/

section FunctionField

variable [NeZero (n : F)]

local notation "A" => W.CoordinateRing

/-- The inclusion `F[W][1/ψₙ] → F(W)`. -/
noncomputable instance : Algebra (AwayPsiN W n) W.FunctionField :=
  (IsLocalization.Away.lift (psiN W n) (g := algebraMap A W.FunctionField)
    (IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2
      (psiN_ne_zero W n)))).toAlgebra

instance : IsScalarTower A (AwayPsiN W n) W.FunctionField :=
  IsScalarTower.of_algebraMap_eq fun a ↦ (IsLocalization.Away.lift_eq (psiN W n) _ a).symm

instance : IsDomain (AwayPsiN W n) :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (psiN_ne_zero W n))

instance : IsFractionRing (AwayPsiN W n) W.FunctionField :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (psiN W n)) _ _

lemma algebraMap_awayPsiN_injective :
    Function.Injective (algebraMap (AwayPsiN W n) W.FunctionField) :=
  IsFractionRing.injective _ _

local notation "ι" => algebraMap (AwayPsiN W n) W.FunctionField
local notation "φ" => algebraMap F W.FunctionField

lemma ι_algebraMap (a : A) :
    ι (algebraMap A (AwayPsiN W n) a) = algebraMap A W.FunctionField a :=
  (IsScalarTower.algebraMap_apply _ _ _ a).symm

lemma ι_algebraMap_base (c : F) : ι (algebraMap F (AwayPsiN W n) c) = φ c := by
  rw [IsScalarTower.algebraMap_apply F A (AwayPsiN W n), ι_algebraMap,
    ← IsScalarTower.algebraMap_apply]

instance : IsScalarTower F (AwayPsiN W n) W.FunctionField :=
  IsScalarTower.of_algebraMap_eq fun c ↦ (ι_algebraMap_base W n c).symm

lemma ι_xAway : ι (xAway W n) = genX W := ι_algebraMap W n _

lemma ι_aeval (p : F[X]) : ι (aeval (xAway W n) p) = aeval (genX W) p := by
  rw [← ι_xAway W n]
  exact (aeval_algHom_apply (IsScalarTower.toAlgHom F (AwayPsiN W n) W.FunctionField) _ p).symm

lemma ι_psiNAway : ι (psiNAway W n) = ((W.map φ).ψ n).evalEval (genX W) (genY W) := by
  rw [WeierstrassCurve.map_ψ, ← genPsi_mk_map_evalEval, ι_algebraMap, psiN]

omit [NeZero (n : F)] in
lemma algebraMap_coordψ₂ : algebraMap A W.FunctionField (coordψ₂ W) =
    2 * genY W + φ W.a₁ * genX W + φ W.a₃ := by
  rw [coordψ₂_eq]
  simp only [map_add, map_mul, map_ofNat, ← IsScalarTower.algebraMap_apply]
  rfl

lemma ι_psiNAway_mul_invPsiNAway : ι (psiNAway W n) * ι (invPsiNAway W n) = 1 := by
  rw [← map_mul, psiNAway_mul_invPsiNAway, map_one]

lemma ι_psiNAway_ne_zero : ι (psiNAway W n) ≠ 0 := by
  intro h
  simpa [h] using ι_psiNAway_mul_invPsiNAway W n

lemma ι_psiNAway_sq : ι (psiNAway W n) ^ 2 = aeval (genX W) (W.ΨSq n) := by
  rw [← map_pow, psiNAway_sq, ι_aeval]

variable [NeZero (2 : F)] [W.IsElliptic]

/-- `x(n • 𝒫)` is transcendental over `F`: the hypothesis of `mulByNEndo`. -/
lemma transcendental_xCoord_nsmul :
    Transcendental F (n • genericPoint (W := W)).xCoord :=
  transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero two_ne_zero
    (intCast_ne_zero_of_neZero n)

lemma ι_xNAway : ι (xNAway W n) = (n • genericPoint (W := W)).xCoord := by
  have h := ι_psiNAway_mul_invPsiNAway W n
  have hp := ι_psiNAway_ne_zero W n
  rw [xCoord_nsmul_genericPoint two_ne_zero (intCast_ne_zero_of_neZero n), xNAway, map_mul,
    map_pow, ι_aeval]
  change _ = aeval (genX W) (W.Φ n) / aeval (genX W) (W.ΨSq n)
  rw [← ι_psiNAway_sq, eq_div_iff (pow_ne_zero 2 hp)]
  linear_combination aeval (genX W) (W.Φ n) * (ι (psiNAway W n) * ι (invPsiNAway W n) + 1) * h

lemma ι_yNAway : ι (yNAway W n) = (n • genericPoint (W := W)).yCoord := by
  have h := ι_psiNAway_mul_invPsiNAway W n
  have hp := ι_psiNAway_ne_zero W n
  have h2 : (2 : W.FunctionField) ≠ 0 := by
    have := (map_ne_zero φ).2 (two_ne_zero (α := F))
    rwa [map_ofNat] at this
  have hε : ι (algebraMap A (AwayPsiN W n) (epsN W n)) = if Even (n : ℤ) then 1 else
      2 * genY W + (W.map φ).a₁ * genX W + (W.map φ).a₃ := by
    rw [ι_algebraMap, epsN, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
    split_ifs
    · exact map_one _
    · exact algebraMap_coordψ₂ W
  rw [yCoord_nsmul_genericPoint two_ne_zero (intCast_ne_zero_of_neZero n),
    WeierstrassCurve.Affine.omegaY, ← hε, ← ι_psiNAway, yNAway]
  simp only [map_mul, map_sub, map_add, map_pow, ι_algebraMap_base, ι_aeval, map_inv₀, map_ofNat,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, WeierstrassCurve.map_Φ,
    WeierstrassCurve.map_ΨSq, WeierstrassCurve.map_preΩ, eval_map, ← aeval_def]
  rw [eq_div_iff (mul_ne_zero h2 (pow_ne_zero 3 hp))]
  field_simp
  linear_combination (ι (algebraMap A (AwayPsiN W n) (epsN W n)) *
      aeval (genX W) (W.preΩ n) -
    ι (psiNAway W n) * φ W.a₁ * aeval (genX W) (W.Φ n) -
    ι (psiNAway W n) * φ W.a₃ * aeval (genX W) (W.ΨSq n)) *
      (ι (psiNAway W n) ^ 2 * ι (invPsiNAway W n) ^ 2 + ι (psiNAway W n) * ι (invPsiNAway W n) +
        1) * h

/-- **The multiplication-by-`n` map** `[n]∗ : F[W] → F[W][1/ψₙ]`, `x ↦ x(n • 𝒫)`,
`y ↦ y(n • 𝒫)`, as a ring homomorphism. -/
noncomputable def mulByNRingHom : A →+* AwayPsiN W n :=
  AdjoinRoot.lift (eval₂RingHom (algebraMap F (AwayPsiN W n)) (xNAway W n)) (yNAway W n) (by
    apply algebraMap_awayPsiN_injective W n
    have hc : RingHom.comp ι (eval₂RingHom (algebraMap F (AwayPsiN W n)) (xNAway W n)) =
        eval₂RingHom φ (n • genericPoint (W := W)).xCoord := by
      refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
      · simp [ι_algebraMap_base]
      · simp [ι_xNAway]
    have h0 := congrArg (mulByNCoordHom (W := W) n (transcendental_xCoord_nsmul W n))
      (AdjoinRoot.mk_self (f := W.polynomial))
    rw [map_zero, mulByNCoordHom, pointCoordHom, AdjoinRoot.lift_mk] at h0
    rw [map_zero, hom_eval₂, ι_yNAway, hc]
    exact h0)

lemma mulByNRingHom_coordX : mulByNRingHom W n (coordX W) = xNAway W n := by
  rw [mulByNRingHom, AdjoinRoot.lift_mk, eval₂_C, coe_eval₂RingHom, eval₂_X]

lemma mulByNRingHom_coordY : mulByNRingHom W n (coordY W) = yNAway W n := by
  rw [mulByNRingHom, AdjoinRoot.lift_root]

lemma mulByNRingHom_algebraMap (c : F) :
    mulByNRingHom W n (algebraMap F A c) = algebraMap F (AwayPsiN W n) c := by
  rw [IsScalarTower.algebraMap_apply F F[X] A, AdjoinRoot.algebraMap_eq, mulByNRingHom,
    AdjoinRoot.lift_of, coe_eval₂RingHom, Polynomial.algebraMap_apply, eval₂_C]
  rfl

/-- **The multiplication-by-`n` map `[n]∗ : F[W] →ₐ[F] F[W][1/ψₙ]`**, the pullback along
`[n] : E ∖ E[n] → E ∖ {O}`. -/
noncomputable def mulByNAlgHom : A →ₐ[F] AwayPsiN W n where
  toRingHom := mulByNRingHom W n
  commutes' := mulByNRingHom_algebraMap W n

lemma mulByNAlgHom_apply (a : A) : mulByNAlgHom W n a = mulByNRingHom W n a := rfl

/-- `[n]∗` followed by `F[W][1/ψₙ] ⊆ F(W)` is the multiplication-by-`n` pullback
`mulByNCoordHom`, defined from `n • 𝒫` in the Mathlib group law. -/
theorem comp_mulByNRingHom :
    RingHom.comp ι (mulByNRingHom W n) =
      mulByNCoordHom (W := W) n (transcendental_xCoord_nsmul W n) := by
  refine AdjoinRoot.ringHom_ext ?_ ?_
  · refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
    · change ι (mulByNRingHom W n (algebraMap F A c)) =
        mulByNCoordHom (W := W) n (transcendental_xCoord_nsmul W n) (algebraMap F A c)
      rw [mulByNRingHom_algebraMap, mulByNCoordHom, pointCoordHom_algebraMap, ι_algebraMap_base]
    · change ι (mulByNRingHom W n (coordX W)) =
        mulByNCoordHom (W := W) n (transcendental_xCoord_nsmul W n) (coordX W)
      rw [mulByNRingHom_coordX, ι_xNAway, mulByNCoordHom, pointCoordHom_X]
  · change ι (mulByNRingHom W n (coordY W)) =
      mulByNCoordHom (W := W) n (transcendental_xCoord_nsmul W n) (coordY W)
    rw [mulByNRingHom_coordY, ι_yNAway, mulByNCoordHom, pointCoordHom_root]

/-- **Compatibility with the function-field pullback**: on `F[W] ⊆ F(W)`, `[n]∗` is
`mulByNEndo n`, the pullback along `P ↦ n • P`. -/
theorem algebraMap_mulByNRingHom (a : A) :
    ι (mulByNRingHom W n a) =
      mulByNEndo (W := W) n (transcendental_xCoord_nsmul W n) (algebraMap A _ a) := by
  rw [← RingHom.comp_apply ι, comp_mulByNRingHom, mulByNEndo, pointEndo_algebraMap]
  rfl

/-- `algebraMap_mulByNRingHom` for the `F`-algebra map `mulByNAlgHom`. -/
theorem algebraMap_mulByNAlgHom (a : A) :
    ι (mulByNAlgHom W n a) =
      mulByNEndo (W := W) n (transcendental_xCoord_nsmul W n) (algebraMap A _ a) :=
  algebraMap_mulByNRingHom W n a

/-- `[n]∗` is injective (`[n]` is dominant). -/
theorem mulByNRingHom_injective : Function.Injective (mulByNRingHom W n) := by
  intro a b h
  apply pointCoordHom_injective _ (transcendental_xCoord_nsmul W n)
  change mulByNCoordHom (W := W) n (transcendental_xCoord_nsmul W n) a =
    mulByNCoordHom (W := W) n (transcendental_xCoord_nsmul W n) b
  rw [← comp_mulByNRingHom, RingHom.comp_apply, RingHom.comp_apply, h]

omit [NeZero (n : F)] [W.IsElliptic] in
lemma two_inv_mul_two_away : algebraMap F (AwayPsiN W n) 2⁻¹ * 2 = 1 := by
  rw [← map_ofNat (algebraMap F (AwayPsiN W n)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero,
    map_one]

/-- `[n]∗ ψ₂ = εₙ preΩₙ(x) / ψₙ³`. -/
lemma mulByNRingHom_coordψ₂ : mulByNRingHom W n (coordψ₂ W) =
    algebraMap A (AwayPsiN W n) (epsN W n) * aeval (xAway W n) (W.preΩ n) *
      invPsiNAway W n ^ 3 := by
  rw [show mulByNRingHom W n (coordψ₂ W) = mulByNRingHom W n _ from
      congrArg (mulByNRingHom W n) (coordψ₂_eq W),
    map_add, map_add, map_mul, map_mul, mulByNRingHom_coordY, mulByNRingHom_algebraMap,
    mulByNRingHom_algebraMap, map_ofNat, mulByNRingHom_coordX, xNAway, yNAway]
  linear_combination (algebraMap A (AwayPsiN W n) (epsN W n) * aeval (xAway W n) (W.preΩ n) -
      psiNAway W n * (algebraMap F (AwayPsiN W n) W.a₁ * aeval (xAway W n) (W.Φ n) +
        algebraMap F (AwayPsiN W n) W.a₃ * aeval (xAway W n) (W.ΨSq n))) *
      invPsiNAway W n ^ 3 * two_inv_mul_two_away W n +
    (-(algebraMap F (AwayPsiN W n) W.a₁ * aeval (xAway W n) (W.Φ n) * invPsiNAway W n ^ 2) -
      algebraMap F (AwayPsiN W n) W.a₃ * (psiNAway W n ^ 2 * invPsiNAway W n ^ 2 +
        psiNAway W n * invPsiNAway W n + 1)) * psiNAway_mul_invPsiNAway W n +
    algebraMap F (AwayPsiN W n) W.a₃ * psiNAway W n * invPsiNAway W n ^ 3 * psiNAway_sq W n

end FunctionField

/-! ### `F[W][1/ψₙ]` as an `F[W]`-algebra via `[n]∗`: finiteness -/

section MulByNAlgebra

variable [NeZero (2 : F)] [NeZero (n : F)] [W.IsElliptic]

local notation "A" => W.CoordinateRing

instance : IsDomain (MulByNCover W n) := inferInstanceAs (IsDomain (AwayPsiN W n))

/-- `MulByNCover W n` is an `F[W]`-algebra through the multiplication-by-`n` map. -/
noncomputable instance : Algebra A (MulByNCover W n) := (mulByNRingHom W n).toAlgebra

instance : IsScalarTower F A (MulByNCover W n) :=
  IsScalarTower.of_algebraMap_eq fun c ↦ (mulByNRingHom_algebraMap W n c).symm

lemma algebraMap_mulByNCover (a : A) :
    algebraMap A (MulByNCover W n) a = toMulByNCover W n (mulByNRingHom W n a) := rfl

lemma isIntegral_toMulByNCover_algebraMap_base (c : F) :
    IsIntegral A (toMulByNCover W n (algebraMap F _ c)) := by
  rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply F A (MulByNCover W n)]
  exact isIntegral_algebraMap

omit [NeZero (2 : F)] [NeZero (n : F)] [W.IsElliptic] in
lemma toMulByNCover_aeval (p : F[X]) :
    toMulByNCover W n (aeval (xAway W n) p) = aeval (toMulByNCover W n (xAway W n)) p :=
  (aeval_algHom_apply (toMulByNCover W n).toAlgHom _ _).symm

lemma isIntegral_xAway : IsIntegral A (toMulByNCover W n (xAway W n)) := by
  refine ⟨(W.Φ n).map (algebraMap F A) - C (coordX W) * (W.ΨSq n).map (algebraMap F A), ?_, ?_⟩
  · refine Monic.sub_of_left ((show (W.Φ n).Monic from W.leadingCoeff_Φ n).map _) ?_
    rw [← smul_eq_C_mul]
    refine (degree_smul_le _ _).trans_lt ?_
    rw [degree_map, degree_map, degree_eq_natDegree (W.Φ_ne_zero n), W.natDegree_Φ,
      Int.natAbs_natCast]
    refine (degree_le_natDegree.trans (WithBot.coe_le_coe.2 (W.natDegree_ΨSq_le n))).trans_lt ?_
    rw [Int.natAbs_natCast]
    exact WithBot.coe_lt_coe.2 (Nat.sub_lt (pow_pos (Nat.pos_of_ne_zero
      (ne_zero_of_neZero_cast (F := F) n)) 2) one_pos)
  · have hc : ∀ p : F[X], eval₂ (algebraMap F (MulByNCover W n))
        (toMulByNCover W n (xAway W n)) p = toMulByNCover W n (aeval (xAway W n) p) := fun p ↦ by
      rw [← aeval_def]
      exact aeval_algHom_apply (toMulByNCover W n).toAlgHom _ _
    rw [eval₂_sub, eval₂_mul, eval₂_C, eval₂_map, eval₂_map, ← IsScalarTower.algebraMap_eq,
      hc, hc, algebraMap_mulByNCover, mulByNRingHom_coordX, ← map_mul, ← map_sub,
      ← xNAway_mul_psiNAway_sq, psiNAway_sq, sub_self, map_zero]

lemma isIntegral_aeval_xAway (p : F[X]) :
    IsIntegral A (toMulByNCover W n (aeval (xAway W n) p)) := by
  induction p using Polynomial.induction_on with
  | C a => rw [aeval_C]; exact isIntegral_toMulByNCover_algebraMap_base W n a
  | add p q hp hq => rw [map_add, map_add]; exact hp.add hq
  | monomial k a h =>
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, map_mul]
    exact h.mul (isIntegral_xAway W n)

lemma isIntegral_xNAway : IsIntegral A (toMulByNCover W n (xNAway W n)) := by
  rw [← mulByNRingHom_coordX, ← algebraMap_mulByNCover]
  exact isIntegral_algebraMap

lemma isIntegral_invPsiNAway : IsIntegral A (toMulByNCover W n (invPsiNAway W n)) := by
  obtain ⟨a, b, h⟩ := exists_invPsiNAway_sq W n
  refine IsIntegral.of_pow two_pos ?_
  rw [← map_pow, h, map_add, map_mul]
  exact ((isIntegral_aeval_xAway W n a).mul (isIntegral_xNAway W n)).add
    (isIntegral_aeval_xAway W n b)

lemma isIntegral_coordψ₂ : IsIntegral A (toMulByNCover W n (algebraMap A _ (coordψ₂ W))) := by
  refine IsIntegral.of_pow two_pos ?_
  rw [← map_pow, ← map_pow, coordψ₂_sq, algebraMap_polynomial_eq_aeval_coordX,
    algebraMap_aeval_coordX]
  exact isIntegral_aeval_xAway W n _

lemma isIntegral_coordY : IsIntegral A (toMulByNCover W n (algebraMap A _ (coordY W))) := by
  have hψ := congrArg (algebraMap A (AwayPsiN W n)) (coordψ₂_eq W)
  simp only [map_add, map_mul, map_ofNat, ← IsScalarTower.algebraMap_apply] at hψ
  have h : algebraMap A (AwayPsiN W n) (coordY W) = algebraMap F (AwayPsiN W n) 2⁻¹ *
      (algebraMap A _ (coordψ₂ W) - algebraMap F (AwayPsiN W n) W.a₁ * xAway W n -
        algebraMap F (AwayPsiN W n) W.a₃) := by
    rw [hψ]
    linear_combination (-algebraMap A (AwayPsiN W n) (coordY W)) * two_inv_mul_two_away W n
  rw [h, map_mul, map_sub, map_sub, map_mul]
  exact (isIntegral_toMulByNCover_algebraMap_base W n _).mul (((isIntegral_coordψ₂ W n).sub
    ((isIntegral_toMulByNCover_algebraMap_base W n _).mul (isIntegral_xAway W n))).sub
      (isIntegral_toMulByNCover_algebraMap_base W n _))

/-- The image of `F[W]` in `F[W][1/ψₙ]` (by localisation) is integral over `F[W]` via `[n]∗`. -/
lemma isIntegral_toMulByNCover_algebraMap (a : A) :
    IsIntegral A (toMulByNCover W n (algebraMap A (AwayPsiN W n) a)) := by
  let S := integralClosure A (MulByNCover W n)
  let ψ : A →+* MulByNCover W n :=
    (toMulByNCover W n).toRingHom.comp (algebraMap A (AwayPsiN W n))
  let f : F[X] →+* S := eval₂RingHom ((algebraMap A S).comp (algebraMap F A))
    ⟨toMulByNCover W n (xAway W n), isIntegral_xAway W n⟩
  have h1 : ψ.comp (algebraMap F[X] A) = S.val.toRingHom.comp f := by
    refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
    · simp only [RingHom.comp_apply, f, coe_eval₂RingHom, eval₂_C]
      change toMulByNCover W n (algebraMap A (AwayPsiN W n) (algebraMap F[X] A (C c))) =
        algebraMap A (MulByNCover W n) (algebraMap F A c)
      rw [algebraMap_mulByNCover, mulByNRingHom_algebraMap, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply F F[X] (AwayPsiN W n)]
      rfl
    · simp only [RingHom.comp_apply, f, coe_eval₂RingHom, eval₂_X]
      rfl
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  have h2 : ψ (AdjoinRoot.mk _ p) =
      S.val (p.eval₂ f ⟨toMulByNCover W n (algebraMap A _ (coordY W)), isIntegral_coordY W n⟩) := by
    rw [← AdjoinRoot.aeval_eq, aeval_def, hom_eval₂, h1]
    exact (hom_eval₂ p f S.val.toRingHom
      ⟨toMulByNCover W n (algebraMap A _ (coordY W)), isIntegral_coordY W n⟩).symm
  exact h2 ▸ (p.eval₂ f ⟨toMulByNCover W n (algebraMap A _ (coordY W)), isIntegral_coordY W n⟩).2

instance : Algebra.IsIntegral A (MulByNCover W n) := by
  refine ⟨fun b ↦ ?_⟩
  obtain ⟨k, a, h⟩ := IsLocalization.Away.surj (psiN W n) ((toMulByNCover W n).symm b)
  have hb : (toMulByNCover W n).symm b =
      algebraMap A (AwayPsiN W n) a * invPsiNAway W n ^ k := by
    rw [← h, mul_assoc, ← mul_pow, psiNAway_mul_invPsiNAway, one_pow, mul_one]
  rw [← (toMulByNCover W n).apply_symm_apply b, hb, map_mul, map_pow]
  exact (isIntegral_toMulByNCover_algebraMap W n a).mul ((isIntegral_invPsiNAway W n).pow k)

/-- **`[n]` is finite**: `F[W][1/ψₙ]` is a finite `F[W]`-module via `[n]∗`. -/
instance : Module.Finite A (MulByNCover W n) :=
  haveI : Algebra.FiniteType F (MulByNCover W n) :=
    inferInstanceAs (Algebra.FiniteType F (AwayPsiN W n))
  haveI := Algebra.FiniteType.of_restrictScalars_finiteType F A (MulByNCover W n)
  Algebra.IsIntegral.finite

end MulByNAlgebra

/-! ### `[n]` is unramified: `[n]∗ω = n ω` -/

section Unramified

variable [NeZero (2 : F)] [NeZero (n : F)] [W.IsElliptic]

local notation "A" => W.CoordinateRing
local notation "M" => MulByNCover W n

omit [NeZero (2 : F)] [NeZero (n : F)] [W.IsElliptic] in
lemma locN_aeval (p : F[X]) : locN W n (aeval (coordX W) p) = aeval (locN W n (coordX W)) p :=
  (aeval_algHom_apply (locN W n) _ p).symm

omit [NeZero (2 : F)] [NeZero (n : F)] [W.IsElliptic] in
lemma deltaN_aeval (p : F[X]) : deltaN W n (aeval (locN W n (coordX W)) p) =
    aeval (locN W n (coordX W)) (derivative p) * locN W n (coordψ₂ W) := by
  rw [Derivation.map_aeval, deltaN_coordX, smul_eq_mul]

omit [NeZero (2 : F)] [NeZero (n : F)] [W.IsElliptic] in
/-- `δ(Φₙ(x)/ψₙ²) = n εₙ preΩₙ(x)/ψₙ³`: the Wronskian identity
`Φₙ' ΨSqₙ - Φₙ ΨSqₙ' = n preΨₙ preΩₙ` is `[n]∗ω = n ω`. -/
lemma deltaN_xN : deltaN W n (aeval (locN W n (coordX W)) (W.Φ n) * invPsiNM W n ^ 2) =
    n * (locN W n (epsN W n) * aeval (locN W n (coordX W)) (W.preΩ n) * invPsiNM W n ^ 3) := by
  rw [sq, Derivation.leibniz, Derivation.leibniz, deltaN_aeval]
  simp only [smul_eq_mul]
  have h1 : locN W n (psiN W n) * invPsiNM W n = 1 := locN_psiN_mul_invPsiNM W n
  have h5 : locN W n (psiN W n) * locN W n (psiN W n) =
      aeval (locN W n (coordX W)) (W.ΨSq n) := by
    rw [← sq, ← map_pow, psiN_sq, algebraMap_polynomial_eq_aeval_coordX, locN_aeval]
  have h2 := congrArg (deltaN W n) h5
  rw [Derivation.leibniz, deltaN_aeval, smul_eq_mul] at h2
  have h3 := congrArg (deltaN W n) h1
  rw [Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul, smul_eq_mul] at h3
  have hW : derivative (W.Φ n) * W.ΨSq n - W.Φ n * derivative (W.ΨSq n) =
      ((n : ℤ) : F[X]) * W.preΨ n * W.preΩ n := W.hasWronskianId n
  have hid := congrArg (aeval (locN W n (coordX W))) hW
  simp only [map_sub, map_mul, map_natCast, Int.cast_natCast] at hid
  have hεψ := congrArg (locN W n) (preΨ_mul_coordψ₂ W n)
  rw [map_mul, map_mul, algebraMap_polynomial_eq_aeval_coordX, locN_aeval] at hεψ
  have hdP2 : 2 * deltaN W n (locN W n (psiN W n)) = aeval (locN W n (coordX W))
      (derivative (W.ΨSq n)) * locN W n (coordψ₂ W) * invPsiNM W n := by
    linear_combination invPsiNM W n * h2 - 2 * deltaN W n (locN W n (psiN W n)) * h1
  have hdU : deltaN W n (invPsiNM W n) =
      -(invPsiNM W n ^ 2 * deltaN W n (locN W n (psiN W n))) := by
    linear_combination invPsiNM W n * h3 - deltaN W n (invPsiNM W n) * h1
  linear_combination 2 * aeval (locN W n (coordX W)) (W.Φ n) * invPsiNM W n * hdU -
    aeval (locN W n (coordX W)) (W.Φ n) * invPsiNM W n ^ 3 * hdP2 -
    aeval (locN W n (coordX W)) (derivative (W.Φ n)) * locN W n (coordψ₂ W) *
      invPsiNM W n ^ 2 * (locN W n (psiN W n) * invPsiNM W n + 1) * h1 +
    aeval (locN W n (coordX W)) (derivative (W.Φ n)) * locN W n (coordψ₂ W) *
      invPsiNM W n ^ 4 * h5 +
    locN W n (coordψ₂ W) * invPsiNM W n ^ 4 * hid +
    n * invPsiNM W n ^ 4 * aeval (locN W n (coordX W)) (W.preΩ n) * hεψ +
    n * locN W n (epsN W n) * aeval (locN W n (coordX W)) (W.preΩ n) * invPsiNM W n ^ 3 * h1

lemma algebraMap_mulByNCover_coordX : algebraMap A M (coordX W) =
    aeval (locN W n (coordX W)) (W.Φ n) * invPsiNM W n ^ 2 := by
  rw [algebraMap_mulByNCover, mulByNRingHom_coordX, xNAway, map_mul, map_pow, toMulByNCover_aeval]
  rfl

lemma algebraMap_mulByNCover_coordψ₂ : algebraMap A M (coordψ₂ W) =
    locN W n (epsN W n) * aeval (locN W n (coordX W)) (W.preΩ n) * invPsiNM W n ^ 3 := by
  rw [algebraMap_mulByNCover, mulByNRingHom_coordψ₂, map_mul, map_mul, map_pow,
    toMulByNCover_aeval]
  rfl

/-- `δ([n]∗ x) = n [n]∗ ψ₂`. -/
lemma deltaN_mulByN_coordX :
    deltaN W n (algebraMap A M (coordX W)) = n * algebraMap A M (coordψ₂ W) := by
  rw [algebraMap_mulByNCover_coordX, algebraMap_mulByNCover_coordψ₂, deltaN_xN]

lemma algebraMap_mulByNCover_injective : Function.Injective (algebraMap A M) :=
  (toMulByNCover W n).injective.comp (mulByNRingHom_injective W n)

/-- `δ([n]∗ y) = -n [n]∗ W_X`, from the Weierstrass equation at `n • 𝒫`. -/
lemma deltaN_mulByN_coordY :
    deltaN W n (algebraMap A M (coordY W)) = -(n * algebraMap A M (coordWX W)) := by
  have heq := congrArg (algebraMap A M) (coord_equation W)
  simp only [map_sub, map_add, map_mul, map_pow, map_zero,
    ← IsScalarTower.algebraMap_apply F A M] at heq
  have hd := congrArg (deltaN W n) heq
  simp only [map_sub, map_add, Derivation.leibniz, Derivation.leibniz_pow,
    Derivation.map_algebraMap, smul_eq_mul, map_zero, nsmul_eq_mul] at hd
  simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, show (3 : ℕ) - 1 = 2 from rfl,
    pow_one] at hd
  have hψ := congrArg (algebraMap A M) (coordψ₂_eq W)
  simp only [map_add, map_mul, map_ofNat, ← IsScalarTower.algebraMap_apply F A M] at hψ
  have hwx := congrArg (algebraMap A M) (rfl : coordWX W = coordWX W)
  conv_rhs at hwx => rw [coordWX]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat,
    ← IsScalarTower.algebraMap_apply F A M] at hwx
  have hx := deltaN_mulByN_coordX W n
  have hne : algebraMap A M (coordψ₂ W) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap_mulByNCover_injective W n)).2 (coordψ₂_ne_zero W)
  have key : algebraMap A M (coordψ₂ W) * (deltaN W n (algebraMap A M (coordY W)) +
      n * algebraMap A M (coordWX W)) = 0 := by
    linear_combination hd + deltaN W n (algebraMap A M (coordY W)) * hψ -
      (algebraMap F M W.a₁ * algebraMap A M (coordY W) - (3 * algebraMap A M (coordX W) ^ 2 +
        2 * algebraMap F M W.a₂ * algebraMap A M (coordX W) + algebraMap F M W.a₄)) * hx +
      n * algebraMap A M (coordψ₂ W) * hwx
  exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.1 key).resolve_left hne)

/-- **`[n]` is unramified**: `Ω[F[W][1/ψₙ]⁄F[W]] = 0`. -/
instance : Algebra.FormallyUnramified A M := by
  rw [Algebra.formallyUnramified_iff]
  let d : Derivation F M (KaehlerDifferential A M) := (KaehlerDifferential.D A M).restrictScalars F
  obtain ⟨c, e, hce⟩ := exists_mul_coordψ₂_add_mul_coordWX W
  have hd : ∀ b, d b = deltaN W n b • (locN W n c • d (locN W n (coordX W)) -
      locN W n e • d (locN W n (coordY W))) := derivation_eq_deltaN_smul W n d hce
  have hx0 : d (algebraMap A M (coordX W)) = 0 := (KaehlerDifferential.D A M).map_algebraMap _
  have hy0 : d (algebraMap A M (coordY W)) = 0 := (KaehlerDifferential.D A M).map_algebraMap _
  rw [hd, deltaN_mulByN_coordX] at hx0
  rw [hd, deltaN_mulByN_coordY] at hy0
  have hce' := congrArg (algebraMap A M) hce
  simp only [map_add, map_mul, map_one] at hce'
  have hN : algebraMap F M (n : F)⁻¹ * (n : M) = 1 := by
    rw [← map_natCast (algebraMap F M), ← map_mul, inv_mul_cancel₀ (NeZero.ne _), map_one]
  have hω : locN W n c • d (locN W n (coordX W)) - locN W n e • d (locN W n (coordY W)) = 0 := by
    linear_combination (norm := module)
      (algebraMap F M (n : F)⁻¹ * algebraMap A M c) • hx0 +
      (-(algebraMap F M (n : F)⁻¹ * algebraMap A M e)) • hy0 -
      hN • (locN W n c • d (locN W n (coordX W)) - locN W n e • d (locN W n (coordY W))) -
      hce' • ((algebraMap F M (n : F)⁻¹ * (n : M)) •
        (locN W n c • d (locN W n (coordX W)) - locN W n e • d (locN W n (coordY W))))
  refine subsingleton_of_forall_eq 0 fun ω ↦ ?_
  have hmem : ω ∈ Submodule.span M (Set.range (KaehlerDifferential.D A M)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  refine Submodule.span_induction (fun _ ⟨b, hb⟩ ↦ ?_) rfl (fun _ _ _ _ h h' ↦ by
    rw [h, h', add_zero]) (fun a _ _ h ↦ by rw [h, smul_zero]) hmem
  rw [← hb]
  change d b = 0
  rw [hd, hω, smul_zero]

/-- **`[n]` is flat**: `F[W]` is a Dedekind domain and `F[W][1/ψₙ]` is torsion-free. -/
instance : Module.Flat A M := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot]
  refine eq_bot_iff.2 fun b hb ↦ ?_
  obtain ⟨⟨a, ha⟩, hab⟩ := (Submodule.mem_torsion_iff b).1 hb
  rw [Submodule.mem_bot]
  rw [Submonoid.smul_def, Algebra.smul_def] at hab
  refine (mul_eq_zero.1 hab).resolve_left ?_
  exact (map_ne_zero_iff _ (algebraMap_mulByNCover_injective W n)).2 (nonZeroDivisors.ne_zero ha)

/-- **`[n] : E ∖ E[n] → E ∖ {O}` is étale**: `F[W][1/ψₙ]` is an étale `F[W]`-algebra via `[n]∗`
(and a finite one, `Module.Finite`). -/
instance : Algebra.Etale A M :=
  haveI : Algebra.FinitePresentation A M :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  Algebra.Etale.of_formallyUnramified_of_flat

end Unramified

end WeierstrassCurve.Affine.CoordinateRing
