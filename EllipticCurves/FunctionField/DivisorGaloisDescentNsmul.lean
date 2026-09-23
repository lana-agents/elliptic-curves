/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.DivisorBaseChange
import EllipticCurves.FunctionField.DivisorConstant
import EllipticCurves.FunctionField.DivisorTransport
import EllipticCurves.FunctionField.FunctionFieldGaloisDescent
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-!
# An `n`-th root of a divisor from the base field descends, by Hilbert 90

Let `K / F` be a **finite Galois** extension and `z ∈ F(W)` nonzero.  If some `g ∈ K(W⁄K)` has
`n · div g = div (functionFieldMap z)` upstairs, then some `g₂ ∈ F(W)` has `n · div g₂ = div z`
**downstairs**.  The witness is not `g` itself and need not be: `g` is unique only up to a constant
of `K`, and `exists_nsmul_divisor_eq_of_functionFieldMap` corrects it by one.

## Why this is a cocycle computation and not a descent of `g`

`div g` is Galois-invariant but `g` is not.  For `σ ∈ Gal(K/F)`, `σ⋆ g` and `g` have the same
divisor, so `c σ := σ⋆ g / g` is a **constant**: `divisor_eq_zero_iff`
(`EllipticCurves.FunctionField.DivisorConstant`) puts it in `Kˣ`.  The family `c` is a `1`-cocycle,
and Noether's form of Hilbert 90 —
`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units` — produces `β : Kˣ` with
`σ β / β = c σ`.  Then `g / β` is fixed by every `σ` and has the same divisor as `g`, so
`exists_ne_zero_functionFieldMap_eq_of_forall_galoisFunctionField_eq`
(`EllipticCurves.FunctionField.FunctionFieldGaloisDescent`) pulls it down to `F(W)`, and
`divisor_eq_of_divisor_functionFieldMap_eq`
(`EllipticCurves.FunctionField.DivisorBaseChange`) brings the identity down with it.

⚠️ **Mathlib's Hilbert 90 takes `[FiniteDimensional F K]` and no `[IsGalois F K]`**, and the `H¹`
spelling is not the one used: `IsMulCocycle₁` and `IsMulCoboundary₁` are elementary predicates
(`∀ g h, f (g * h) = g • f h * f g` and `∃ x, ∀ g, g • x / x = f g`) and no group-cohomology API is
needed to consume them.  `[IsGalois F K]` is needed here, but by the **descent** step and not by
Hilbert 90.

## Main statements

* `WeierstrassCurve.Affine.CoordinateRing.divisor_galoisFunctionField_eq_of_nsmul_divisor_eq` —
  the divisor of such a `g` is Galois-invariant, at every `n ≠ 0` and with **no** finiteness or
  Galois hypothesis on `K / F` at all.
* `WeierstrassCurve.Affine.CoordinateRing.exists_nsmul_divisor_eq_of_functionFieldMap` — the
  descent, for `[FiniteDimensional F K]` and `[IsGalois F K]`, at every `n ≠ 0`.

## ⚠️ What is *not* here

* **No index is fixed.** Both statements are at an arbitrary `n ≠ 0` and neither mentions `[2]` or
  `[3]`.  The `n = 2` consumer is `EllipticCurves.FunctionField.PullbackPrincipalityTwoGeneral`;
  ⚠️ **at `n = 3` nothing here is the obstruction** — what is missing there is the tower, not the
  descent.
* **`n ≠ 0` is load-bearing and is the only arithmetic hypothesis.** It is what cancels `n` from
  `n · ord_w (σ⋆ g) = n · ord_w g`; there is no hypothesis on the characteristic of `F` anywhere
  below, and in particular none of the form `(n : F) ≠ 0`.
* **Nothing here produces `g`.** Both statements take the `n`-th root upstairs as a hypothesis;
  where it comes from is the consumer's business.
* **No ramification index is computed.** `divisor_eq_of_divisor_functionFieldMap_eq` needs only
  `e ≠ 0`, which is why this file states no `e = 1` claim and needs none — the `e = 1` bullet of
  `EllipticCurves.FunctionField.DivisorBaseChange`'s `## What is *not* here` is untouched by this
  file and is still true of that file.
* **`Nat.card Gal(K/F)` is never used**, and no statement below counts automorphisms.

## References

* [Silverman, *The arithmetic of elliptic curves*][silverman2009], VIII.2 (Hilbert 90 and the
  Kummer sequence); X.1 for the cocycle form used here.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

namespace CoordinateRing

variable (K : Type*) [Field K] [Algebra F K]

/-- **The divisor of an `n`-th root of a divisor from the base field is Galois-invariant**, at every
`n ≠ 0` and over an arbitrary extension `K / F` — neither finite nor Galois is assumed here.

`div (functionFieldMap z)` is invariant because `σ⋆` fixes the image of `functionFieldMap`
(`galoisFunctionField_functionFieldMap`), and `n · ord_w (σ⋆ g) = n · ord_w g` then cancels.  ⚠️ The
cancellation is the whole use of `hn`: it is `n ≠ 0` in `ℤ` on the *coefficients*, not `(n : F) ≠ 0`
in the base field. -/
theorem divisor_galoisFunctionField_eq_of_nsmul_divisor_eq {n : ℕ} (hn : n ≠ 0)
    {z : W.FunctionField} {g : (W⁄K).FunctionField}
    (h : n • divisor (W⁄K) g = divisor (W⁄K) (functionFieldMap W K z))
    (σ : K ≃ₐ[F] K) :
    divisor (W⁄K) (galoisFunctionField σ g) = divisor (W⁄K) g := by
  ext w
  have hz : ord ((mapEquiv (galoisCoordRing σ)).symm w) (functionFieldMap W K z)
      = ord w (functionFieldMap W K z) := by
    rw [← ord_galoisFunctionField_apply σ w, galoisFunctionField_functionFieldMap]
  have hw := congrArg (fun D => D w) h
  have hw' := congrArg (fun D => D ((mapEquiv (galoisCoordRing σ)).symm w)) h
  simp only [Finsupp.smul_apply, divisor_apply, nsmul_eq_mul] at hw hw'
  rw [divisor_apply, divisor_apply, ord_galoisFunctionField_apply]
  have : (n : ℤ) * ord ((mapEquiv (galoisCoordRing σ)).symm w) g = (n : ℤ) * ord w g := by
    rw [hw', hz, hw]
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hn) this

/-- **Hilbert 90 turns an `n`-th root of `div z` over a finite Galois `K / F` into one over `F`.**

Given nonzero `z ∈ F(W)` and `g ∈ K(W⁄K)` with `n · div g = div (functionFieldMap z)`, there is a
nonzero `g₂ ∈ F(W)` with `n · div g₂ = div z`.

⚠️ **`g₂` is not the descent of `g`** — `g` itself is generally not in the image of
`functionFieldMap`.  What descends is `g / β` for the `β : Kˣ` that Hilbert 90 produces, and a
constant does not move a divisor (`divisor_algebraMap_base`), so the identity survives the
correction. -/
theorem exists_nsmul_divisor_eq_of_functionFieldMap [FiniteDimensional F K] [IsGalois F K]
    {n : ℕ} (hn : n ≠ 0) {z : W.FunctionField} (hz : z ≠ 0)
    {g : (W⁄K).FunctionField} (hg : g ≠ 0)
    (h : n • divisor (W⁄K) g = divisor (W⁄K) (functionFieldMap W K z)) :
    ∃ g₂ : W.FunctionField, g₂ ≠ 0 ∧ n • divisor W g₂ = divisor W z := by
  classical
  have hgσ : ∀ σ : K ≃ₐ[F] K, galoisFunctionField σ g ≠ 0 := fun σ =>
    fun hzero => hg (by simpa using (galoisFunctionField (W := W) σ).injective (hzero.trans
      (map_zero (galoisFunctionField (W := W) σ)).symm))
  -- the constant `c σ` with `σ⋆ g = c σ · g`
  have hc : ∀ σ : K ≃ₐ[F] K, ∃ c : Kˣ,
      galoisFunctionField σ g = algebraMap K (W⁄K).FunctionField (c : K) * g := by
    intro σ
    have h0 : divisor (W⁄K) (galoisFunctionField σ g / g) = 0 := by
      rw [divisor_div (hgσ σ) hg, divisor_galoisFunctionField_eq_of_nsmul_divisor_eq K hn h σ,
        sub_self]
    obtain ⟨c, hc0, hceq⟩ :=
      exists_eq_algebraMap_of_divisor_eq_zero (div_ne_zero (hgσ σ) hg) h0
    exact ⟨Units.mk0 c hc0, by rw [Units.val_mk0, ← hceq, div_mul_cancel₀ _ hg]⟩
  choose cc hcc using hc
  -- it is a `1`-cocycle
  have hinj : Function.Injective (algebraMap K (W⁄K).FunctionField) :=
    (algebraMap K (W⁄K).FunctionField).injective
  have hcocycle : groupCohomology.IsMulCocycle₁ cc := by
    intro σ τ
    have key : algebraMap K (W⁄K).FunctionField ((cc (σ * τ) : K))
        = algebraMap K (W⁄K).FunctionField ((σ (cc τ : K)) * (cc σ : K)) := by
      have h1 : galoisFunctionField (σ * τ) g
          = algebraMap K (W⁄K).FunctionField ((σ (cc τ : K)) * (cc σ : K)) * g := by
        rw [galoisFunctionField_mul_apply, hcc τ, map_mul, galoisFunctionField_algebraMap,
          hcc σ, map_mul]
        ring
      have h2 := (hcc (σ * τ)).symm.trans h1
      exact mul_right_cancel₀ hg h2
    exact Units.ext (by simpa using hinj key)
  -- Hilbert 90
  obtain ⟨β, hβ⟩ :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units cc hcocycle
  -- the invariant function `g₁`
  set g₁ : (W⁄K).FunctionField := g / algebraMap K (W⁄K).FunctionField (β : K) with hg₁def
  have hβ0 : algebraMap K (W⁄K).FunctionField (β : K) ≠ 0 := fun hzero =>
    β.ne_zero (hinj (hzero.trans (map_zero _).symm))
  have hg₁0 : g₁ ≠ 0 := div_ne_zero hg hβ0
  have hg₁inv : ∀ σ : K ≃ₐ[F] K, galoisFunctionField σ g₁ = g₁ := by
    intro σ
    have hcσ : (σ (β : K)) = (cc σ : K) * (β : K) := by
      have h' : σ • β = cc σ * β := div_eq_iff_eq_mul.mp (hβ σ)
      simpa [AlgEquiv.smul_units_def] using congrArg (fun u : Kˣ => (u : K)) h'
    rw [hg₁def, map_div₀, hcc σ, galoisFunctionField_algebraMap, hcσ, map_mul]
    rw [mul_comm (algebraMap K (W⁄K).FunctionField (cc σ : K))
      (algebraMap K (W⁄K).FunctionField (β : K))]
    rw [mul_comm (algebraMap K (W⁄K).FunctionField (cc σ : K)) g]
    rw [mul_div_mul_right _ _ (fun hzero =>
      (cc σ).ne_zero (hinj (hzero.trans (map_zero _).symm)))]
  have hdivg₁ : divisor (W⁄K) g₁ = divisor (W⁄K) g := by
    obtain ⟨c, hc0, hceq⟩ : ∃ c : K, c ≠ 0 ∧ (β : K) = c := ⟨(β : K), β.ne_zero, rfl⟩
    rw [hg₁def, divisor_div hg hβ0, hceq, divisor_algebraMap_base hc0, sub_zero]
  -- descend `g₁`
  obtain ⟨g₂, hg₂0, hg₂⟩ :=
    exists_ne_zero_functionFieldMap_eq_of_forall_galoisFunctionField_eq (W := W) hg₁0 hg₁inv
  refine ⟨g₂, hg₂0, ?_⟩
  have hup : ((n : ℤ)) • divisor (W⁄K) (functionFieldMap W K g₂)
      = divisor (W⁄K) (functionFieldMap W K z) := by
    rw [hg₂, hdivg₁, ← h, natCast_zsmul]
  have := divisor_eq_of_divisor_functionFieldMap_eq (W := W) (K := K) hz hg₂0 hup
  rwa [natCast_zsmul] at this

end CoordinateRing

end WeierstrassCurve.Affine
