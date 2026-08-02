/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FormalGroup.InvariantDifferentialLaurent
import EllipticCurves.FormalGroup.WThreeFunctionalEq
import EllipticCurves.FormalGroup.GenuineLawTransfer
import EllipticCurves.FormalGroup.LaurentMap
import EllipticCurves.FormalGroup.LaurentDerivation
import EllipticCurves.FormalGroup.GenuineLawMap
import EllipticCurves.FormalGroup.LogAdditivity
import EllipticCurves.FormalGroup.Law
import EllipticCurves.FormalGroup.ExpansionSubst
import EllipticCurves.FormalGroup.UniversalIdentification

/-!
# The genuine identification `w ∘ F_E = -y₃⁻¹` (issue #333)

This file proves, unconditionally over every `CommRing R`, the identity

`HahnSeries.embedDoubleLaurent (W.formalW.subst W.formalGroupZW) = W.formalWThree`,

i.e. the Laurent image of the sum-point `w`-series `w ∘ F_E` equals the transported third
`w`-coordinate `W₃ = -y₃⁻¹`.  This is the single remaining identity of the Laurent route to the
invariant-differential invariance `(★)` (issue #315), and the sole gate on the formal-group cascade.

## Strategy

Both `WeierstrassCurve.embedDoubleLaurent_formalW_subst_formalGroupZW_functional_eq`
(`EllipticCurves.FormalGroup.InvariantDifferentialLaurent`) and
`WeierstrassCurve.formalWThree_functional_eq` (`EllipticCurves.FormalGroup.WThreeFunctionalEq`)
establish that `u₁ := embedDoubleLaurent (w ∘ F_E)` and `u₂ := W₃` satisfy the **identical**
Weierstrass functional equation with parameter `F_E = W.formalGroupLaurent`.  Subtracting the two
equations factors as `(u₁ - u₂)·B = 0`, where `B` is the derivative-like bracket.  Over the
**universal curve** `univ : WeierstrassCurve (MvPolynomial (Fin 5) ℤ)`
(`EllipticCurves.FormalGroup.UniversalIdentification`), the domain
`((MvPolynomial (Fin 5) ℤ)⸨X⸩)⸨X⸩` has no zero divisors and `B ≠ 0` (its bi-`z`-constant coefficient
is `1`), forcing `u₁ = u₂`.  Base change along `W.specialize` then gives the general statement.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1.
-/

open scoped LaurentSeries
open HahnSeries

namespace WeierstrassCurve

variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

/-! ### Base-change map lemmas -/

/-- Naturality of the third `w`-coordinate `W₃ = -y₃⁻¹` under base change:
`Ψ f W.formalWThree = (W.map f).formalWThree`. -/
theorem map_formalWThree (f : R →+* S) :
    HahnSeries.mapRingHom (HahnSeries.mapRingHom f) W.formalWThree = (W.map f).formalWThree := by
  rw [formalWThree, formalWThree, map_neg,
    RingHom.map_ringInverse _ _ W.isUnit_formalYThree, W.map_formalYThree f]

/-- Naturality of the sum-point `w`-series `w ∘ F` under base change:
`MvPowerSeries.map f (W.formalW.subst W.formalGroupZW)
  = (W.map f).formalW.subst (W.map f).formalGroupZW`. -/
theorem map_formalW_subst_formalGroupZW (f : R →+* S) :
    MvPowerSeries.map f (W.formalW.subst W.formalGroupZW)
      = (W.map f).formalW.subst (W.map f).formalGroupZW := by
  rw [PowerSeries.map_subst W.hasSubst_formalGroupZW W.formalW, W.map_formalW f,
    W.map_formalGroupZW f]

/-! ### Part B — the bracket is nonzero over the universal domain -/

/-- `coeff`-at-`0` of a product of two Hahn series with support in `ℕ` (no strictly negative
coefficients) is the product of their `coeff`-at-`0`'s: the only antidiagonal pair summing to `0`
with both entries `≥ 0` is `(0, 0)`. -/
private lemma coeff_zero_mul_of_nonneg {K : Type*} [CommRing K] {x y : HahnSeries ℤ K}
    (hx : ∀ n : ℤ, n < 0 → x.coeff n = 0) (hy : ∀ n : ℤ, n < 0 → y.coeff n = 0) :
    (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_single (0, 0) ?_ ?_
  · rintro ⟨i, j⟩ hmem hne
    rw [Finset.mem_antidiagonal] at hmem
    obtain ⟨hi, hj, hij⟩ := hmem
    rcases lt_trichotomy i 0 with h | h | h
    · rw [hx i h, zero_mul]
    · exact absurd (Prod.ext h (by omega : j = 0)) hne
    · rw [hy j (by omega), mul_zero]
  · intro hnotmem
    by_contra hprod
    exact hnotmem (Finset.mem_antidiagonal.mpr
      ⟨(HahnSeries.mem_support _ _).mpr (left_ne_zero_of_mul hprod),
       (HahnSeries.mem_support _ _).mpr (right_ne_zero_of_mul hprod), by ring⟩)

/-- Peeling the double constant `C (C a)` off the bi-`0` coefficient. -/
private lemma coeff_zero_coeff_zero_C2_mul (a : MvPolynomial (Fin 5) ℤ)
    (x : ((MvPolynomial (Fin 5) ℤ)⸨X⸩)⸨X⸩) :
    ((HahnSeries.C (HahnSeries.C a) * x).coeff 0).coeff 0 = a * (x.coeff 0).coeff 0 := by
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul, HahnSeries.C_apply,
    HahnSeries.coeff_single_zero_mul]

/-- If one factor has vanishing bi-`0` coefficient and both factors are supported in `ℕ` in each
grading, the product's bi-`0` coefficient vanishes. -/
private lemma coeff_zero_coeff_zero_mul_left {x y : ((MvPolynomial (Fin 5) ℤ)⸨X⸩)⸨X⸩}
    (hx : ∀ n : ℤ, n < 0 → x.coeff n = 0) (hy : ∀ n : ℤ, n < 0 → y.coeff n = 0)
    (hxi : ∀ n : ℤ, n < 0 → (x.coeff 0).coeff n = 0)
    (hyi : ∀ n : ℤ, n < 0 → (y.coeff 0).coeff n = 0)
    (hbx : (x.coeff 0).coeff 0 = 0) :
    ((x * y).coeff 0).coeff 0 = 0 := by
  rw [coeff_zero_mul_of_nonneg hx hy, coeff_zero_mul_of_nonneg hxi hyi, hbx, zero_mul]

/-- **The uniqueness bracket is nonzero over the universal curve.**  In the domain
`((MvPolynomial (Fin 5) ℤ)⸨X⸩)⸨X⸩`, the bracket obtained by subtracting the two Weierstrass
functional equations at `u₁ = embedDoubleLaurent (w ∘ F_E)` and `u₂ = W₃` is nonzero, because its
bi-`z`-constant coefficient is `1` (every subtracted summand carries positive order in one grading:
`F.coeff 0 = z₁`, `u₁ = w ∘ F` has order `≥ 3`, and `u₂ = -y₃⁻¹` has inner order `3`). -/
private lemma bracket_univ_ne_zero :
    (1
        - (HahnSeries.C (HahnSeries.C univ.a₁) * univ.formalGroupLaurent
            + HahnSeries.C (HahnSeries.C univ.a₂) * univ.formalGroupLaurent ^ 2)
        - (HahnSeries.C (HahnSeries.C univ.a₃)
            + HahnSeries.C (HahnSeries.C univ.a₄) * univ.formalGroupLaurent)
          * (HahnSeries.embedDoubleLaurent (univ.formalW.subst univ.formalGroupZW)
              + univ.formalWThree)
        - HahnSeries.C (HahnSeries.C univ.a₆)
          * (HahnSeries.embedDoubleLaurent (univ.formalW.subst univ.formalGroupZW) ^ 2
              + HahnSeries.embedDoubleLaurent (univ.formalW.subst univ.formalGroupZW)
                  * univ.formalWThree
              + univ.formalWThree ^ 2))
      ≠ (0 : ((MvPolynomial (Fin 5) ℤ)⸨X⸩)⸨X⸩) := by
  set F := univ.formalGroupLaurent with hFdef
  set u₁ := HahnSeries.embedDoubleLaurent (univ.formalW.subst univ.formalGroupZW) with hu1def
  set u₂ := univ.formalWThree with hu2def
  -- `F = F_E` is pole-free in both gradings, with `F.coeff 0 = z₁` (bi-const `0`).
  have hF0 : F.coeff 0 = HahnSeries.single (1 : ℤ) 1 := univ.coeff_formalGroupLaurent_zero
  have hFneg : ∀ n : ℤ, n < 0 → F.coeff n = 0 := by
    intro n hn
    rw [hFdef, ← univ.embedDoubleLaurent_formalGroupZW, HahnSeries.coeff_embedDoubleLaurent,
      if_pos hn]
  have hFin : ∀ n : ℤ, n < 0 → (F.coeff 0).coeff n = 0 := by
    intro n hn; rw [hF0, HahnSeries.coeff_single_of_ne (by omega : (n : ℤ) ≠ 1)]
  have hFbc : (F.coeff 0).coeff 0 = 0 := by
    rw [hF0, HahnSeries.coeff_single_of_ne (by norm_num : (0 : ℤ) ≠ 1)]
  -- `u₁ = w ∘ F` is pole-free with vanishing (bi-)constant coefficient.
  have hu1neg : ∀ n : ℤ, n < 0 → u₁.coeff n = 0 := by
    intro n hn; rw [hu1def, HahnSeries.coeff_embedDoubleLaurent, if_pos hn]
  have hu1val : u₁.coeff 0 = HahnSeries.ofPowerSeries ℤ _ (PowerSeries.mk fun m =>
      MvPowerSeries.coeff (Finsupp.single 0 m + Finsupp.single 1 ((0 : ℤ).natAbs))
        (univ.formalW.subst univ.formalGroupZW)) := by
    rw [hu1def, HahnSeries.coeff_embedDoubleLaurent, if_neg (by norm_num : ¬ (0 : ℤ) < 0)]
  have hu1in : ∀ n : ℤ, n < 0 → (u₁.coeff 0).coeff n = 0 := by
    intro n hn; rw [hu1val]; exact coe_powerSeries_coeff_of_neg _ hn
  have hu1bc : (u₁.coeff 0).coeff 0 = 0 := by
    have hcc : MvPowerSeries.constantCoeff (univ.formalW.subst univ.formalGroupZW) = 0 := by
      rw [← MvPowerSeries.one_le_order_iff_constCoeff_eq_zero]
      exact univ.one_le_order_formalW_subst
        (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr univ.constantCoeff_formalGroupZW)
    rw [hu1val, PowerSeries.coeff_coe, if_neg (by norm_num : ¬ (0 : ℤ) < 0), PowerSeries.coeff_mk]
    simpa using hcc
  -- `u₂ = -y₃⁻¹` has outer order `0` and inner order `3` (via `y₃ · w = -1`, `order y₃ = -3`).
  have hYT_ne : univ.formalYThree ≠ 0 :=
    HahnSeries.orderTop_ne_top.mp (by rw [univ.orderTop_formalYThree]; exact WithTop.zero_ne_top)
  have hYTord : univ.formalYThree.order = 0 := by
    have h : (univ.formalYThree.order : WithTop ℤ) = (0 : WithTop ℤ) := by
      rw [HahnSeries.order_eq_orderTop_of_ne_zero hYT_ne, univ.orderTop_formalYThree]
    exact_mod_cast h
  have hYT0 : univ.formalYThree.coeff 0 = univ.formalY := by
    rw [show (0 : ℤ) = univ.formalYThree.order from hYTord.symm, ← HahnSeries.leadingCoeff_eq,
      univ.leadingCoeff_formalYThree]
  have hYW : univ.formalYThree * u₂ = -1 := by
    rw [hu2def, formalWThree, mul_neg, Ring.mul_inverse_cancel _ univ.isUnit_formalYThree]
  have hYTneg : ∀ n : ℤ, n < 0 → univ.formalYThree.coeff n = 0 := fun n hn =>
    HahnSeries.coeff_eq_zero_of_lt_orderTop (by rw [univ.orderTop_formalYThree]; exact_mod_cast hn)
  have hu2ne : u₂ ≠ 0 := by
    intro h; rw [h, mul_zero] at hYW; exact (neg_ne_zero.mpr one_ne_zero) hYW.symm
  have hu2ord : u₂.order = 0 := by
    have hlc : univ.formalYThree.leadingCoeff * u₂.leadingCoeff ≠ 0 :=
      mul_ne_zero (by rwa [ne_eq, HahnSeries.leadingCoeff_eq_zero])
        (by rwa [ne_eq, HahnSeries.leadingCoeff_eq_zero])
    have h2 := HahnSeries.order_mul_of_ne_zero hlc
    rw [hYW, hYTord, zero_add] at h2
    have hone : (-1 : ((MvPolynomial (Fin 5) ℤ)⸨X⸩)⸨X⸩).order = 0 := by simp [HahnSeries.order_neg]
    rw [hone] at h2; exact h2.symm
  have hu2neg : ∀ n : ℤ, n < 0 → u₂.coeff n = 0 := fun n hn =>
    HahnSeries.coeff_eq_zero_of_lt_order (by rw [hu2ord]; exact hn)
  have hprod0 : univ.formalY * u₂.coeff 0 = -1 := by
    have h := coeff_zero_mul_of_nonneg hYTneg hu2neg
    rw [hYW, hYT0] at h
    rw [← h]; simp [HahnSeries.coeff_neg, HahnSeries.coeff_one]
  have hYne : univ.formalY ≠ 0 := univ.isUnit_formalY.ne_zero
  have hwne : u₂.coeff 0 ≠ 0 := by
    intro h; rw [h, mul_zero] at hprod0; exact (neg_ne_zero.mpr one_ne_zero) hprod0.symm
  have hYord_le : univ.formalY.order ≤ -3 := by
    have h1 : univ.formalY.orderTop ≤ (-3 : ℤ) :=
      HahnSeries.orderTop_le_of_coeff_ne_zero (by rw [univ.coeff_formalY_neg_three]; norm_num)
    have h2 : (univ.formalY.order : WithTop ℤ) = univ.formalY.orderTop :=
      HahnSeries.order_eq_orderTop_of_ne_zero hYne
    have h3 : (univ.formalY.order : WithTop ℤ) ≤ (-3 : ℤ) := by rw [h2]; exact h1
    exact_mod_cast h3
  have hwge : 3 ≤ (u₂.coeff 0).order := by
    have hlcY : univ.formalY.leadingCoeff * (u₂.coeff 0).leadingCoeff ≠ 0 :=
      mul_ne_zero (by rwa [ne_eq, HahnSeries.leadingCoeff_eq_zero])
        (by rwa [ne_eq, HahnSeries.leadingCoeff_eq_zero])
    have hword := HahnSeries.order_mul_of_ne_zero hlcY
    rw [hprod0] at hword
    have hone : (-1 : (MvPolynomial (Fin 5) ℤ)⸨X⸩).order = 0 := by simp [HahnSeries.order_neg]
    rw [hone] at hword; omega
  have hu2bc : (u₂.coeff 0).coeff 0 = 0 := HahnSeries.coeff_eq_zero_of_lt_order (by omega)
  have hu2in : ∀ n : ℤ, n < 0 → (u₂.coeff 0).coeff n = 0 := fun n hn =>
    HahnSeries.coeff_eq_zero_of_lt_order (by omega)
  -- bi-`0` coefficients of the nine monomials all vanish.
  have pFF := coeff_zero_coeff_zero_mul_left hFneg hFneg hFin hFin hFbc
  have pu1u1 := coeff_zero_coeff_zero_mul_left hu1neg hu1neg hu1in hu1in hu1bc
  have pu2u2 := coeff_zero_coeff_zero_mul_left hu2neg hu2neg hu2in hu2in hu2bc
  have pFu1 := coeff_zero_coeff_zero_mul_left hFneg hu1neg hFin hu1in hFbc
  have pFu2 := coeff_zero_coeff_zero_mul_left hFneg hu2neg hFin hu2in hFbc
  have pu1u2 := coeff_zero_coeff_zero_mul_left hu1neg hu2neg hu1in hu2in hu1bc
  -- The bi-`0` coefficient of the bracket is `1`, so the bracket is nonzero.
  intro hB
  have hBeq : (1
      - (HahnSeries.C (HahnSeries.C univ.a₁) * F + HahnSeries.C (HahnSeries.C univ.a₂) * F ^ 2)
      - (HahnSeries.C (HahnSeries.C univ.a₃) + HahnSeries.C (HahnSeries.C univ.a₄) * F)
        * (u₁ + u₂)
      - HahnSeries.C (HahnSeries.C univ.a₆) * (u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2))
      = 1 - (HahnSeries.C (HahnSeries.C univ.a₁) * F
          + HahnSeries.C (HahnSeries.C univ.a₂) * (F * F)
          + HahnSeries.C (HahnSeries.C univ.a₃) * u₁
          + HahnSeries.C (HahnSeries.C univ.a₃) * u₂
          + HahnSeries.C (HahnSeries.C univ.a₄) * (F * u₁)
          + HahnSeries.C (HahnSeries.C univ.a₄) * (F * u₂)
          + HahnSeries.C (HahnSeries.C univ.a₆) * (u₁ * u₁)
          + HahnSeries.C (HahnSeries.C univ.a₆) * (u₁ * u₂)
          + HahnSeries.C (HahnSeries.C univ.a₆) * (u₂ * u₂)) := by ring
  rw [hBeq] at hB
  have h1 := congrArg
    (fun z : ((MvPolynomial (Fin 5) ℤ)⸨X⸩)⸨X⸩ => (z.coeff 0).coeff 0) hB
  simp only [HahnSeries.coeff_sub, HahnSeries.coeff_add, coeff_zero_coeff_zero_C2_mul, hFbc, pFF,
    hu1bc, hu2bc, pFu1, pFu2, pu1u1, pu1u2, pu2u2, mul_zero, add_zero, sub_zero,
    HahnSeries.coeff_one, HahnSeries.coeff_zero] at h1
  exact absurd h1 (by norm_num)

/-! ### Part C — the universal-domain identification -/

/-- **The genuine identification over the universal curve.**
`embedDoubleLaurent (univ.formalW.subst univ.formalGroupZW) = univ.formalWThree`. -/
theorem embedDoubleLaurent_formalW_subst_formalGroupZW_univ :
    HahnSeries.embedDoubleLaurent (univ.formalW.subst univ.formalGroupZW) = univ.formalWThree := by
  have h₁ := univ.embedDoubleLaurent_formalW_subst_formalGroupZW_functional_eq
  have h₂ := univ.formalWThree_functional_eq
  have hdiff :
      (HahnSeries.embedDoubleLaurent (univ.formalW.subst univ.formalGroupZW) - univ.formalWThree)
        * (1
            - (HahnSeries.C (HahnSeries.C univ.a₁) * univ.formalGroupLaurent
                + HahnSeries.C (HahnSeries.C univ.a₂) * univ.formalGroupLaurent ^ 2)
            - (HahnSeries.C (HahnSeries.C univ.a₃)
                + HahnSeries.C (HahnSeries.C univ.a₄) * univ.formalGroupLaurent)
              * (HahnSeries.embedDoubleLaurent (univ.formalW.subst univ.formalGroupZW)
                  + univ.formalWThree)
            - HahnSeries.C (HahnSeries.C univ.a₆)
              * (HahnSeries.embedDoubleLaurent (univ.formalW.subst univ.formalGroupZW) ^ 2
                  + HahnSeries.embedDoubleLaurent (univ.formalW.subst univ.formalGroupZW)
                      * univ.formalWThree
                  + univ.formalWThree ^ 2)) = 0 := by
    linear_combination h₁ - h₂
  rcases mul_eq_zero.mp hdiff with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h bracket_univ_ne_zero

/-! ### Part D — base change to an arbitrary base ring -/

/-- **The genuine identification `w ∘ F_E = -y₃⁻¹`** over an arbitrary `CommRing R`, obtained from
the universal-domain identity by base change along `W.specialize`. -/
theorem embedDoubleLaurent_formalW_subst_formalGroupZW (W : WeierstrassCurve R) :
    HahnSeries.embedDoubleLaurent (W.formalW.subst W.formalGroupZW) = W.formalWThree := by
  have key := congrArg (HahnSeries.mapRingHom (HahnSeries.mapRingHom W.specialize))
    embedDoubleLaurent_formalW_subst_formalGroupZW_univ
  rwa [HahnSeries.map_embedDoubleLaurent, univ.map_formalW_subst_formalGroupZW W.specialize,
    univ.map_formalWThree W.specialize, univ_map_specialize] at key

end WeierstrassCurve
