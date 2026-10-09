/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

/-!
# `ψₙ ≡ Ψₙ` and `ψₙ² ≡ ΨSqₙ` modulo `4·polynomial`, not merely modulo `polynomial`

Mathlib's `WeierstrassCurve.Affine.CoordinateRing.mk_ψ` and `…mk_Ψ_sq` say that in the coordinate
ring `R[X][Y]/(W.polynomial)`,

```
ψₙ = Ψₙ          and        ψₙ² = ΨSqₙ ,
```

at every index over every commutative ring.  Read back in `R[X][Y]` each is a divisibility by
`W.polynomial`: `ψₙ² − ΨSqₙ = Dₙ·polynomial` for some `Dₙ`.  **This file sharpens both to a
divisibility by `4·W.polynomial`**, at every index over every commutative ring and with no
hypotheses at all.

## Why the factor `4` is worth a file

⚠️ **A consumer that has to cancel a `4` cannot use the coordinate-ring form.**  Clearing the
denominators of an identity in the division-polynomial coordinates `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` produces a
polynomial identity in which `ψₙ²` has to be traded for `ΨSqₙ`, and the trade leaves a multiple of
`W.polynomial` behind.  If that multiple is only known to be `Dₙ·polynomial` then the `4` of the
completed-square form `(2Y + a₁X + a₃)² = 4X³ + b₂X² + 2b₄X + b₆` cannot be divided out even over a
characteristic-`0` domain, because `Dₙ` is not known to be even; if it is known to be
`4·Dₙ·polynomial` then it can.  `EllipticCurves.Torsion.OmegaOnCurveCharFree` is that consumer, and
the `4` here is exactly what makes its cancellation legal.

## The mechanism, in one sentence

`ψₙ = normEDS ψ₂ Ψ₃ preΨ₄ n` and `Ψₙ = preΨₙ·(if Even n then ψ₂ else 1)` with
`preΨₙ = preNormEDS Ψ₂Sq² Ψ₃ preΨ₄ n`, so the **only** difference between the two is the
substitution `ψ₂² ↦ ΨSq₂ = Ψ₂Sq` in the first argument of the recursion — and Mathlib's `ψ₂_sq`
says those two differ by exactly `4·W.polynomial`.  ⚠️ **So Mathlib's own proof of `mk_ψ` runs
verbatim in the quotient by `4·W.polynomial`**: `map_preNormEDS` transports the whole recursion
along any ring homomorphism, and the quotient map is one.  Nothing about the recursion is unfolded
here and no induction is run.

## Main statements

⚠️ Every public declaration of this file is listed: **3 public, 0 private, 3 listed.**

* `WeierstrassCurve.four_mul_polynomial_dvd_ψ_sub_Ψ` : `4·polynomial ∣ ψₙ − Ψₙ`.
* `WeierstrassCurve.four_mul_polynomial_dvd_Ψ_sq_sub_C_ΨSq` : `4·polynomial ∣ Ψₙ² − ΨSqₙ`, which is
  the parity factor's own square and needs no recursion at all.
* `WeierstrassCurve.four_mul_polynomial_dvd_ψ_sq_sub_C_ΨSq` : `4·polynomial ∣ ψₙ² − ΨSqₙ`, the form
  the consumer wants.

⚠️ **Nothing in Mathlib is restated or weakened**: `mk_ψ` and `mk_Ψ_sq` are the coordinate-ring
statements, these are the sharpened `R[X][Y]` ones, and the first is used in the proof of the third
only through the quotient map it is itself proved by.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], Exercise 3.7.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- **`4·W.polynomial ∣ ψₙ − Ψₙ`**, at every index over every commutative ring, with no hypotheses.

This is Mathlib's `WeierstrassCurve.Affine.CoordinateRing.mk_ψ` with the modulus sharpened from
`W.polynomial` to `4·W.polynomial`, and the proof is that one run in the quotient by the sharper
ideal: the two sides differ only in the substitution `ψ₂² ↦ Ψ₂Sq` inside `preNormEDS`, the quotient
map is a ring homomorphism and so commutes with the recursion (`map_preNormEDS`), and `ψ₂_sq` puts
`ψ₂² − Ψ₂Sq = 4·W.polynomial` in the ideal. -/
theorem four_mul_polynomial_dvd_ψ_sub_Ψ (n : ℤ) :
    4 * W.toAffine.polynomial ∣ W.ψ n - W.Ψ n := by
  set I : Ideal R[X][Y] := Ideal.span {4 * W.toAffine.polynomial} with hI
  set q := Ideal.Quotient.mk I with hq
  have hψ₂ : q W.ψ₂ ^ 2 = q (C W.Ψ₂Sq) := by
    rw [← map_pow, Ideal.Quotient.eq, hI, Ideal.mem_span_singleton]
    exact ⟨1, by rw [ψ₂_sq]; ring⟩
  have key : q (W.ψ n) = q (W.Ψ n) := by
    simp_rw [WeierstrassCurve.ψ, normEDS, WeierstrassCurve.Ψ, preΨ, map_mul, map_preNormEDS,
      map_pow, ← hψ₂, ← pow_mul]
  rw [Ideal.Quotient.eq, hI, Ideal.mem_span_singleton] at key
  exact key

/-- **`4·W.polynomial ∣ Ψₙ² − ΨSqₙ`**, at every index over every commutative ring, with no
hypotheses.

⚠️ **No recursion is involved**: `Ψₙ = preΨₙ·(if Even n then ψ₂ else 1)` and
`ΨSqₙ = preΨₙ²·(if Even n then Ψ₂Sq else 1)` have the *same* `preΨₙ`, so the difference is
`preΨₙ²·(ψ₂² − Ψ₂Sq)` at even `n` and `0` at odd `n`, and `ψ₂_sq` evaluates the bracket. -/
theorem four_mul_polynomial_dvd_Ψ_sq_sub_C_ΨSq (n : ℤ) :
    4 * W.toAffine.polynomial ∣ W.Ψ n ^ 2 - C (W.ΨSq n) := by
  rw [WeierstrassCurve.Ψ, ΨSq]
  split_ifs with h
  · refine ⟨C (W.preΨ n) ^ 2, ?_⟩
    rw [C_mul, C_pow]
    linear_combination C (W.preΨ n) ^ 2 * W.ψ₂_sq
  · refine ⟨0, ?_⟩
    rw [C_mul, C_pow, C_1, mul_one, mul_one, mul_zero, sub_self]

/-- **`4·W.polynomial ∣ ψₙ² − ΨSqₙ`**, at every index over every commutative ring, with no
hypotheses — the form a denominator-clearing consumer wants.

`ψₙ² − ΨSqₙ = (ψₙ − Ψₙ)(ψₙ + Ψₙ) + (Ψₙ² − ΨSqₙ)`, and both summands are divisible by
`4·W.polynomial` by the two theorems above. -/
theorem four_mul_polynomial_dvd_ψ_sq_sub_C_ΨSq (n : ℤ) :
    4 * W.toAffine.polynomial ∣ W.ψ n ^ 2 - C (W.ΨSq n) := by
  obtain ⟨E, hE⟩ := W.four_mul_polynomial_dvd_ψ_sub_Ψ n
  obtain ⟨E', hE'⟩ := W.four_mul_polynomial_dvd_Ψ_sq_sub_C_ΨSq n
  exact ⟨(W.ψ n + W.Ψ n) * E + E', by linear_combination (W.ψ n + W.Ψ n) * hE + hE'⟩

end WeierstrassCurve
