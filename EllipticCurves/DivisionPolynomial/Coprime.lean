/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

/-!
# `Φ₂`, `Ψ₃` and `Ψ₂Sq` are coprime — an explicit Bézout certificate over `Δ²`

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

## Main results

* `WeierstrassCurve.Φ_two_eq` — `Φ₂ = X·Ψ₂Sq − Ψ₃` (**relocated** here from
  `EllipticCurves.Torsion.DoublingSurjective`, which now imports it);
* `WeierstrassCurve.bezout_Φ_two_Ψ₂Sq` and `WeierstrassCurve.bezout_Ψ₃_Ψ₂Sq` — the certificates;
* **`WeierstrassCurve.isCoprime_Φ_two_Ψ₂Sq`** and **`WeierstrassCurve.isCoprime_Ψ₃_Ψ₂Sq`** — the
  coprimality, for `[W.IsElliptic]`.

## What is *not* here

* The general `IsCoprime (W.Φ n) (W.ΨSq n)`. Only `n = 2` is proved; the general case is a much
  larger induction and is not needed by the consumer below.
* Any statement about roots, torsion points, or `n • P = O ↔ Ψₙ = 0`.
* Anything about `RatFunc`, function fields, or the degree of `[2]`. The consumer is the middle step
  of the tower computing `[F(W) : [2]∗F(W)] = 4`, which reads `Φ₂/Ψ₂Sq` as a reduced fraction and
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

end IsElliptic

end WeierstrassCurve
