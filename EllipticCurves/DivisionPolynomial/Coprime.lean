/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

/-!
# Coprimality of division polynomials: `(Φ₂, Ψ₂Sq)`, `(Ψ₃, Ψ₂Sq)` and `(Φ₃, ΨSq₃)`

For a Weierstrass curve `W` over a commutative ring, the division polynomials

```
Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆,     Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈,
Φ₂   = X⁴ − b₄X² − 2b₆X − b₈ = X·Ψ₂Sq − Ψ₃
```

satisfy an explicit Bézout identity with right-hand side `Δ²`:

```lean
bezout_Φ_two_Ψ₂Sq : W.bezoutΦTwo * W.Φ 2 + W.bezoutΨ₂Sq * W.Ψ₂Sq = C (W.Δ ^ 2)
```

Hence when `Δ` is a unit — in particular for `[W.IsElliptic]` — the pairs `(Φ₂, Ψ₂Sq)` and
`(Ψ₃, Ψ₂Sq)` are **coprime**.

Geometrically the second statement says that no point of `W` is both `2`-torsion and `3`-torsion,
which is exactly what fails on a singular curve; and indeed the identity is *false* without `Δ`, so
the discriminant is genuinely load-bearing rather than decorative.

The pair `(Φ₃, ΨSq₃)` is here too, and it is **not** obtained the same way — see the section on the
`n = 3` certificate below.

## Why an explicit certificate rather than a root argument

The classical proof is "a common root would be a point that is both `2`- and `3`-torsion, hence
`O`, which is not affine". That argument needs the torsion characterisation
`n • P = O ↔ Ψₙ(x P) = 0`, which is a substantial separate development. The Bézout certificate
needs none of it, works over an arbitrary commutative ring, and is checked by `ring1`.

Mathlib has no coprimality statement anywhere under
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/` (checked against `v4.32.0`), so
everything here is new; it is an upstream candidate, since nothing
below mentions function fields, places or divisors.

## Where the certificate comes from, and the one subtlety

`bezoutΦTwo` and `bezoutΨ₂Sq` are the cofactors produced by the adjugate of the Sylvester matrix of
the pair, so the identity they satisfy in the **free** polynomial ring `ℤ[b₂, b₄, b₆, b₈][X]` has
right-hand side the resultant

```
Res(Ψ₂Sq, Φ₂) = b₂⁴b₈² − 6b₂³b₄b₆b₈ + … − 256b₈³
```

which is **not** `Δ²` there — `b₂, b₄, b₆, b₈` are not independent. The two differ by an explicit
multiple of `4b₈ − b₂b₆ + b₄²`, which vanishes by Mathlib's `WeierstrassCurve.b_relation`. That is
why the proof below is a `linear_combination` against `b_relation` rather than a bare `ring1`: the
identity is true for Weierstrass curves and false for free `b`-parameters.

Because the relation is used in the form `4b₈ = b₂b₆ − b₄²` and never divided by, **nothing here
needs `2` or `3` to be invertible**; the results hold in every characteristic.

## The `n = 3` certificate is a congruence, not a resultant

A Bézout identity for `(Φ₃, ΨSq₃)` itself is not viable: `deg Φ₃ = 9` and `deg ΨSq₃ = 8`, so the
Sylvester matrix is `17 × 17` and its adjugate cofactors are polynomials no `ring1` call would
survive. What replaces it, in `preΨ₄_sq_eq_Ψ₂Sq_pow_add_Ψ₃_mul`, is the congruence

```
preΨ₄² ≡ Ψ₂Sq⁴   (mod Ψ₃),
```

which is `ψ₂(2P) = ψ₄(P)/ψ₂(P)⁴` read univariately and then reduced by `Φ₂ = X·Ψ₂Sq − Ψ₃`; its
cofactor is a five-term expression in `X`, `Ψ₂Sq` and `Ψ₃`. From it, `isCoprime_Ψ₃_Ψ₂Sq` alone
gives `IsCoprime preΨ₄ Ψ₃`, and `Φ₃ = X·Ψ₃² − preΨ₄·Ψ₂Sq` with `ΨSq₃ = Ψ₃²` finishes.

So the discriminant still does all the work at `n = 3`, but only through the `n = 2` certificate:
**no new Bézout identity is computed**, and the two `Δ²`-certificates above remain the only ones in
this file.

## Main results

* `WeierstrassCurve.Φ_two_eq` — `Φ₂ = X·Ψ₂Sq − Ψ₃` (**relocated** here from
  `EllipticCurves.Torsion.DoublingSurjective`, which now imports it);
* `WeierstrassCurve.bezout_Φ_two_Ψ₂Sq` and `WeierstrassCurve.bezout_Ψ₃_Ψ₂Sq` — the certificates;
* `WeierstrassCurve.preΨ₄_sq_eq_Ψ₂Sq_pow_add_Ψ₃_mul` — the `n = 3` congruence, over an arbitrary
  commutative ring;
* **`WeierstrassCurve.isCoprime_Φ_two_Ψ₂Sq`**, **`WeierstrassCurve.isCoprime_Ψ₃_Ψ₂Sq`**,
  `WeierstrassCurve.isCoprime_preΨ₄_Ψ₃` and **`WeierstrassCurve.isCoprime_Φ_three_ΨSq_three`** —
  the coprimality, for `[W.IsElliptic]`.

## What is *not* here

* The general `IsCoprime (W.Φ n) (W.ΨSq n)`. Only `n = 2` and `n = 3` are proved, each by its own
  ad-hoc certificate; the general case is a much larger induction and no consumer needs it yet.
* Any statement about roots, torsion points, or `n • P = O ↔ Ψₙ = 0`.
* Anything about `RatFunc`, function fields, or the degree of `[n]`. The consumers are the middle
  steps of the towers computing `[F(W) : [2]∗F(W)] = 4` and `[F(W) : [3]∗F(W)] = 9`, in
  `EllipticCurves.FunctionField.MulByTwoDegree` and
  `EllipticCurves.FunctionField.MulByThreeDegree`; each reads `Φₙ/ΨSqₙ` as a reduced fraction and
  needs exactly the coprimality proved here.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.
* L. Washington, *Elliptic Curves: Number Theory and Cryptography*, §3.2.
-/

open Polynomial

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### The Bézout cofactors -/

/-- The cofactor of `Φ₂` in the Bézout identity `bezout_Φ_two_Ψ₂Sq`.  It is the `Φ₂`-part of the
adjugate of the Sylvester matrix of the pair `(Ψ₂Sq, Φ₂)`. -/
noncomputable def bezoutΦTwo : R[X] :=
  C (-8 * W.b₂ ^ 2 * W.b₄ ^ 2 + 8 * W.b₂ ^ 3 * W.b₆ + 288 * W.b₄ ^ 3 - 336 * W.b₂ * W.b₄ * W.b₆
      + 16 * W.b₂ ^ 2 * W.b₈ + 1296 * W.b₆ ^ 2 - 384 * W.b₄ * W.b₈)
      * X ^ 2
    + C (-2 * W.b₂ ^ 3 * W.b₄ ^ 2 + 2 * W.b₂ ^ 4 * W.b₆ + 72 * W.b₂ * W.b₄ ^ 3
      - 80 * W.b₂ ^ 2 * W.b₄ * W.b₆ - 144 * W.b₄ ^ 2 * W.b₆ + 360 * W.b₂ * W.b₆ ^ 2
      + 32 * W.b₂ * W.b₄ * W.b₈ - 576 * W.b₆ * W.b₈)
      * X
    + C (-4 * W.b₂ ^ 2 * W.b₄ ^ 3 + 5 * W.b₂ ^ 3 * W.b₄ * W.b₆ - W.b₂ ^ 4 * W.b₈ + 144 * W.b₄ ^ 4
      - 204 * W.b₂ * W.b₄ ^ 2 * W.b₆ + W.b₂ ^ 2 * W.b₆ ^ 2 + 48 * W.b₂ ^ 2 * W.b₄ * W.b₈
      + 864 * W.b₄ * W.b₆ ^ 2 - 384 * W.b₄ ^ 2 * W.b₈ - 176 * W.b₂ * W.b₆ * W.b₈ + 256 * W.b₈ ^ 2)

/-- The cofactor of `Ψ₂Sq` in the Bézout identity `bezout_Φ_two_Ψ₂Sq`. -/
noncomputable def bezoutΨ₂Sq : R[X] :=
  C (2 * W.b₂ ^ 2 * W.b₄ ^ 2 - 2 * W.b₂ ^ 3 * W.b₆ - 72 * W.b₄ ^ 3 + 84 * W.b₂ * W.b₄ * W.b₆
      - 4 * W.b₂ ^ 2 * W.b₈ - 324 * W.b₆ ^ 2 + 96 * W.b₄ * W.b₈)
      * X ^ 3
    + C (-W.b₂ ^ 2 * W.b₄ * W.b₆ + W.b₂ ^ 3 * W.b₈ + 36 * W.b₄ ^ 2 * W.b₆ - 9 * W.b₂ * W.b₆ ^ 2
      - 32 * W.b₂ * W.b₄ * W.b₈ + 144 * W.b₆ * W.b₈)
      * X ^ 2
    + C (-2 * W.b₂ ^ 2 * W.b₄ ^ 3 + 2 * W.b₂ ^ 3 * W.b₄ * W.b₆ + 72 * W.b₄ ^ 4
      - 84 * W.b₂ * W.b₄ ^ 2 * W.b₆ + 2 * W.b₂ ^ 2 * W.b₆ ^ 2 + 2 * W.b₂ ^ 2 * W.b₄ * W.b₈
      + 270 * W.b₄ * W.b₆ ^ 2 - 48 * W.b₄ ^ 2 * W.b₈ + 8 * W.b₂ * W.b₆ * W.b₈ - 64 * W.b₈ ^ 2)
      * X
    + C (-3 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ + 4 * W.b₂ ^ 3 * W.b₆ ^ 2 - W.b₂ ^ 3 * W.b₄ * W.b₈
      + 108 * W.b₄ ^ 3 * W.b₆ - 162 * W.b₂ * W.b₄ * W.b₆ ^ 2 + 36 * W.b₂ * W.b₄ ^ 2 * W.b₈
      + 7 * W.b₂ ^ 2 * W.b₆ * W.b₈ + 729 * W.b₆ ^ 3 - 432 * W.b₄ * W.b₆ * W.b₈
      + 16 * W.b₂ * W.b₈ ^ 2)

/-! ### The identities -/

/-- **`Φ₂ = X · Ψ₂Sq - Ψ₃`.** Both sides are `X⁴ - b₄X² - 2b₆X - b₈`: the `X³` terms of `X · Ψ₂Sq`
and `Ψ₃` agree, and the remaining coefficients differ by `2b₄ - 3b₄ = -b₄` and `b₆ - 3b₆ = -2b₆`.

It is also what transfers the Bézout certificate below from `Φ₂` to `Ψ₃`.

**Relocated, not new.**  This lemma was proved in `EllipticCurves.Torsion.DoublingSurjective`; it is
a general fact about `Φ`, `Ψ₂Sq` and `Ψ₃` over an arbitrary commutative ring, with no torsion point
in it, so it belongs at the bottom of the import hierarchy rather than in the torsion tree.  That
file now imports it from here; the proof is unchanged. -/
lemma Φ_two_eq : W.Φ 2 = X * W.Ψ₂Sq - W.Ψ₃ := by
  rw [Φ_two, Ψ₂Sq, Ψ₃]
  simp only [map_ofNat, C_mul]
  ring1

/-- **The Bézout certificate for `Φ₂` and `Ψ₂Sq`, with right-hand side `Δ²`.**

The cofactors come from the Sylvester adjugate, so in the free ring `ℤ[b₂, b₄, b₆, b₈][X]` the
combination equals the resultant, not `Δ²`; the two differ by a multiple of `4b₈ − b₂b₆ + b₄²`,
which is `0` by `b_relation`.  That multiple is the `linear_combination` coefficient below. -/
theorem bezout_Φ_two_Ψ₂Sq :
    W.bezoutΦTwo * W.Φ 2 + W.bezoutΨ₂Sq * W.Ψ₂Sq = C (W.Δ ^ 2) := by
  have hb : (4 : R[X]) * C W.b₈ = C W.b₂ * C W.b₆ - C W.b₄ ^ 2 := by
    have h := congrArg (C : R →+* R[X]) W.b_relation
    simp only [map_ofNat, C_sub, C_mul, C_pow] at h
    exact h
  rw [bezoutΦTwo, bezoutΨ₂Sq, Φ_two, Ψ₂Sq, Δ]
  C_simp
  linear_combination (norm := ring1)
    (-64 * C W.b₄ ^ 4 + 80 * C W.b₂ * C W.b₄ ^ 2 * C W.b₆ - 4 * C W.b₂ ^ 2 * C W.b₆ ^ 2
     - 12 * C W.b₂ ^ 2 * C W.b₄ * C W.b₈ - 324 * C W.b₄ * C W.b₆ ^ 2 + 112 * C W.b₄ ^ 2 * C W.b₈
     + 32 * C W.b₂ * C W.b₆ * C W.b₈ - 64 * C W.b₈ ^ 2)
      * hb

/-- **The Bézout certificate for `Ψ₃` and `Ψ₂Sq`**, obtained from `bezout_Φ_two_Ψ₂Sq` through
`Φ_two_eq`. -/
theorem bezout_Ψ₃_Ψ₂Sq :
    (-W.bezoutΦTwo) * W.Ψ₃ + (W.bezoutΦTwo * X + W.bezoutΨ₂Sq) * W.Ψ₂Sq = C (W.Δ ^ 2) := by
  have h := W.bezout_Φ_two_Ψ₂Sq
  rw [W.Φ_two_eq] at h
  linear_combination h

/-! ### The `n = 3` certificate, via a congruence rather than a resultant -/

/-- **`preΨ₄² ≡ Ψ₂Sq⁴ modulo Ψ₃`**, with the cofactor written out.

The naive route to `IsCoprime (Φ₃) (ΨSq₃)` is a Bézout certificate for the pair itself, whose
Sylvester matrix is `17 × 17`; the resultant has weight `48` in `b₂, …, b₈` and neither it nor its
cofactors is a polynomial a `ring1` call would survive.  This congruence replaces the whole of it,
and it is small because it is a *composite* of two facts already in the tree:

* `ψ₂(2P) = ψ₄(P)/ψ₂(P)⁴` — in univariate form, `preΨ₄²` is `Ψ₂Sq` evaluated at the duplication
  fraction `Φ₂/Ψ₂Sq`, cleared of denominators:
  `preΨ₄² = 4Φ₂³ + b₂Φ₂²Ψ₂Sq + 2b₄Φ₂Ψ₂Sq² + b₆Ψ₂Sq³`;
* `Φ_two_eq`, i.e. `Φ₂ = X·Ψ₂Sq − Ψ₃`.

Substituting the second into the first and discarding every term carrying a factor `Ψ₃` leaves
`Ψ₂Sq³·(4X³ + b₂X² + 2b₄X + b₆) = Ψ₂Sq⁴`; what is discarded is `Ψ₃` times the cofactor below.
Geometrically: a point with `Ψ₃(x) = 0` has `2P = −P`, so `ψ₂(2P)² = ψ₂(P)²` up to the fourth power
of `ψ₂(P)` coming from the denominator — a `4`-torsion point is never `3`-torsion.

As with `bezout_Φ_two_Ψ₂Sq` the identity is **false** in the free ring `ℤ[b₂, b₄, b₆, b₈][X]` and
holds only against `b_relation`, which is why the proof is a `linear_combination` and not a
`ring1`; the correction term is the explicit degree-`8` multiplier below.  Nothing is divided by, so
this holds in every characteristic. -/
theorem preΨ₄_sq_eq_Ψ₂Sq_pow_add_Ψ₃_mul :
    W.preΨ₄ ^ 2 = W.Ψ₂Sq ^ 4 + W.Ψ₃ *
      ((12 * X + C W.b₂) * W.Ψ₂Sq * W.Ψ₃ - 4 * W.Ψ₃ ^ 2
        - (12 * X ^ 2 + C (2 * W.b₂) * X + C (2 * W.b₄)) * W.Ψ₂Sq ^ 2) := by
  have hb : (4 : R[X]) * C W.b₈ = C W.b₂ * C W.b₆ - C W.b₄ ^ 2 := by
    have h := congrArg (C : R →+* R[X]) W.b_relation
    simp only [map_ofNat, C_sub, C_mul, C_pow] at h
    exact h
  rw [preΨ₄, Ψ₂Sq, Ψ₃]
  C_simp
  linear_combination (norm := ring1)
    (13 * X ^ 8 + 8 * C W.b₂ * X ^ 7 + 28 * C W.b₄ * X ^ 6 + C W.b₂ ^ 2 * X ^ 6
      + 38 * C W.b₆ * X ^ 5 + 6 * C W.b₂ * C W.b₄ * X ^ 5 + 22 * C W.b₈ * X ^ 4
      + 8 * C W.b₄ ^ 2 * X ^ 4 + 7 * C W.b₂ * C W.b₆ * X ^ 4 + 16 * C W.b₄ * C W.b₆ * X ^ 3
      + 4 * C W.b₂ * C W.b₈ * X ^ 3 + 7 * C W.b₆ ^ 2 * X ^ 2 + 8 * C W.b₄ * C W.b₈ * X ^ 2
      + 6 * C W.b₆ * C W.b₈ * X + C W.b₈ ^ 2) * hb

/-! ### Coprimality -/

section IsElliptic

variable [W.IsElliptic]

/-- Any Bézout combination landing on `C (Δ²)` witnesses coprimality, because `Δ` is a unit. -/
private theorem isCoprime_of_eq_C_Δ_sq {a b p q : R[X]}
    (h : a * p + b * q = C (W.Δ ^ 2)) : IsCoprime p q := by
  obtain ⟨w, hw⟩ := (W.isUnit_Δ.pow 2).map (C : R →+* R[X])
  refine ⟨(↑w⁻¹ : R[X]) * a, (↑w⁻¹ : R[X]) * b, ?_⟩
  have hring : (↑w⁻¹ : R[X]) * a * p + (↑w⁻¹ : R[X]) * b * q
      = (↑w⁻¹ : R[X]) * (a * p + b * q) := by ring
  rw [hring, h, ← hw, ← Units.val_mul, inv_mul_cancel, Units.val_one]

/-- **`Φ₂` and `Ψ₂Sq` are coprime** on an elliptic curve. -/
theorem isCoprime_Φ_two_Ψ₂Sq : IsCoprime (W.Φ 2) W.Ψ₂Sq :=
  W.isCoprime_of_eq_C_Δ_sq W.bezout_Φ_two_Ψ₂Sq

/-- **`Ψ₃` and `Ψ₂Sq` are coprime** on an elliptic curve: no point is both `2`-torsion and
`3`-torsion.  This is the statement that fails on a singular curve. -/
theorem isCoprime_Ψ₃_Ψ₂Sq : IsCoprime W.Ψ₃ W.Ψ₂Sq :=
  W.isCoprime_of_eq_C_Δ_sq W.bezout_Ψ₃_Ψ₂Sq

/-- **`preΨ₄` and `Ψ₃` are coprime** on an elliptic curve: no point is simultaneously of order
dividing `4` but not `2`, and of order `3`.

The certificate is the congruence `preΨ₄² ≡ Ψ₂Sq⁴ (mod Ψ₃)` together with `isCoprime_Ψ₃_Ψ₂Sq`; no
Bézout identity for this pair is computed. -/
theorem isCoprime_preΨ₄_Ψ₃ : IsCoprime W.preΨ₄ W.Ψ₃ := by
  have h : IsCoprime (W.preΨ₄ ^ 2) W.Ψ₃ := by
    rw [W.preΨ₄_sq_eq_Ψ₂Sq_pow_add_Ψ₃_mul]
    exact (W.isCoprime_Ψ₃_Ψ₂Sq.symm.pow_left).add_mul_left_left _
  exact h.of_isCoprime_of_dvd_left (dvd_pow_self _ two_ne_zero)

/-- **`Φ₃` and `ΨSq₃` are coprime** on an elliptic curve — the reduced-fraction hypothesis that the
degree computation `[F(x) : F(x₃)] = 9` needs of `x(3P) = Φ₃/ΨSq₃`.

`ΨSq₃ = Ψ₃²`, so it suffices to be coprime to `Ψ₃`; and `Φ₃ = X·Ψ₃² − preΨ₄·Ψ₂Sq` is congruent to
`−preΨ₄·Ψ₂Sq` modulo `Ψ₃`, where both factors are coprime to `Ψ₃` — the second by
`isCoprime_Ψ₃_Ψ₂Sq`, the first by `isCoprime_preΨ₄_Ψ₃`. -/
theorem isCoprime_Φ_three_ΨSq_three : IsCoprime (W.Φ 3) (W.ΨSq 3) := by
  have hΦ : W.Φ 3 = -(W.preΨ₄ * W.Ψ₂Sq) + W.Ψ₃ * (X * W.Ψ₃) := by
    rw [WeierstrassCurve.Φ_three]; ring1
  have h : IsCoprime (W.Φ 3) W.Ψ₃ := by
    rw [hΦ]
    exact ((W.isCoprime_preΨ₄_Ψ₃.mul_left W.isCoprime_Ψ₃_Ψ₂Sq.symm).neg_left).add_mul_left_left _
  rw [WeierstrassCurve.ΨSq_three]
  exact h.pow_right

end IsElliptic

end WeierstrassCurve
