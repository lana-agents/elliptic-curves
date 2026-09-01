/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.OmegaUniversal
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.RingTheory.Localization.FractionRing

/-!
# `HasPreΩSq` reduces to its EVALUATED form over a characteristic-`0` field

`EllipticCurves.Torsion.OmegaUniversal` reduces the univariate identity
`WeierstrassCurve.HasPreΩSq n`, quantified over every commutative ring and every curve, to the
single instance at `WeierstrassCurve.univQ` over `MvPolynomial (Fin 5) ℚ`.  This file takes the
reduction one step further, in the direction that matters for actually proving it.

`EllipticCurves.Torsion.OmegaOnCurve` carries **two** forms of the identity: the polynomial
`HasPreΩSq n`, an equation in `R[X]`, and the evaluated `HasPreΩSqAt n x`, the same equation at one
`x : R`.  The polynomial form implies the evaluated one at every point (`HasPreΩSq.at`); at a
single `x` there is no way back.  Over an **infinite integral domain** there is:
two polynomials agreeing at every point of such a ring are equal (`Polynomial.funext`).  Composed
with the universal reduction, that gives

**`HasPreΩSq n` for every curve over every commutative ring, from the EVALUATED identity at every
point of every characteristic-`0` field.**

## Why that is the useful direction

The two forms are not equally expensive, and `OmegaOnCurve`'s module docstring already measured the
gap at `n = 3`.  The polynomial identity there is true over `ℤ`, but `4b₈ = b₂b₆ − b₄²` is not a
legal substitution over an arbitrary ring, so `ring1` must run with the `aᵢ` as atoms — **9903
monomials in six atoms**, which closed only outside the build and was killed by `lake build` with
exit `137`, out of memory.  With `2` invertible, `b₈` is eliminated by division by `4` and the same
identity has **545 monomials** and closes in seconds.  That is exactly what
`WeierstrassCurve.Affine.hasPreΩSqAt_three` does, and it is why that lemma is stated over a field
of characteristic `≠ 2` and in the evaluated form only.

So the characteristic hypothesis was never a restriction on the *statement*; it was a restriction
on the *proof*, and the universal reduction removes it.  `hasPreΩSq_three` below is the first
cash-out: the polynomial identity at `n = 3`, over **every** commutative ring, including where
`2 = 0`, with no new algebra at all.

## Main results

* `WeierstrassCurve.hasPreΩSq_of_forall_hasPreΩSqAt` : over an infinite integral domain, the
  evaluated identity at every point gives the polynomial identity.
* `WeierstrassCurve.hasPreΩSq_of_forall_charZero` : if the polynomial identity holds for every
  curve over every characteristic-`0` field, it holds for every curve over every commutative ring.
* `WeierstrassCurve.hasPreΩSq_of_forall_hasPreΩSqAt_charZero` : the two composed, and the form in
  which `#404`'s crux should now be attacked.
* `WeierstrassCurve.hasPreΩSq_three` : `HasPreΩSq 3`, for every curve over every commutative ring.

## ⚠️ What this settles and what it does not

**`#404` is not closed.**  Its crux is `HasPreΩSq` at *general* `n`.  This file closes `n = 3` and
re-poses the general question in a strictly weaker form: it is now enough to prove the **evaluated**
identity at every point of a characteristic-`0` field, where `2`, `3` and `4` are units and the
545-monomial route is legal.  `hasPreΩSq_of_forall_hasPreΩSqAt_charZero` is that statement and is
the durable content here; `hasPreΩSq_three` is one instance of it.

⚠️ **This is not the circular route, and the distinction is easy to lose.**
`EllipticCurves.Torsion.OmegaUniversal`'s docstring warns that a generic-point argument is where
the entanglement with `#251` lives, because the classical proof identifies `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` with
the group-law multiple `n • P`.  That warning is about how one *proves* the evaluated identity at a
new index.  It does not touch the *upgrade* from evaluated to polynomial, which is what this file
is: base change and `Polynomial.funext`, with **no group law, no `n • P` and no `#251` input**.
Read literally the warning would say this route is blocked; it is not.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], Exercise 3.7, III.6.
-/

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

/-! ### From the evaluated identity to the polynomial one -/

/-- **The converse of `HasPreΩSq.at`, over an infinite integral domain.**  The two sides of
`HasPreΩSq n` are polynomials in `R[X]`; if they agree at every `x : R` and `R` is an infinite
domain, they are equal.  ⚠️ Infiniteness is essential and is not a technicality — over a finite
ring the evaluated identity at every point says nothing about the polynomials. -/
theorem hasPreΩSq_of_forall_hasPreΩSqAt [IsDomain R] [Infinite R] {W : WeierstrassCurve R} {n : ℤ}
    (h : ∀ x : R, W.HasPreΩSqAt n x) : W.HasPreΩSq n := by
  rw [HasPreΩSq]
  refine Polynomial.funext fun x => ?_
  have hx := h x
  rw [HasPreΩSqAt] at hx
  simpa only [eval_mul, eval_pow, eval_add, eval_ofNat, eval_C, apply_ite (Polynomial.eval x),
    eval_one] using hx

/-! ### The reduction to characteristic `0` -/

/-- The universal base of `WeierstrassCurve.univQ`. -/
private abbrev UnivBase : Type := MvPolynomial (Fin 5) ℚ

/-- Its fraction field: a characteristic-`0` field, hence an infinite domain, into which the
universal base injects.  It is `private` because no consumer should ever need to name it — the
reduction below quantifies over all characteristic-`0` fields. -/
private abbrev UnivFrac : Type := FractionRing UnivBase

private instance : CharZero UnivFrac :=
  charZero_of_injective_algebraMap (IsFractionRing.injective UnivBase UnivFrac)

/-- **`HasPreΩSq n` over every characteristic-`0` field gives it over every commutative ring.**
Instantiate the hypothesis at the fraction field of `MvPolynomial (Fin 5) ℚ`, descend along the
injection to `univQ`, then specialise with `hasPreΩSq_of_univQ`.

The hypothesis is stated at `Type` because that is where `univQ` and its fraction field live; the
conclusion is universe-polymorphic. -/
theorem hasPreΩSq_of_forall_charZero {n : ℤ}
    (h : ∀ (F : Type) [Field F] [CharZero F] (V : WeierstrassCurve F), V.HasPreΩSq n)
    (W : WeierstrassCurve R) : W.HasPreΩSq n :=
  hasPreΩSq_of_univQ
    (hasPreΩSq_of_map (f := algebraMap UnivBase UnivFrac)
      (IsFractionRing.injective UnivBase UnivFrac) (h UnivFrac _)) W

/-- **The form in which `#404`'s crux should now be attacked.**  To prove the polynomial identity
`HasPreΩSq n` for every Weierstrass curve over every commutative ring it is enough to prove the
**evaluated** identity `HasPreΩSqAt n x` at every point of every characteristic-`0` field — where
`2`, `3` and `4` are units, `b₈ = (b₂b₆ − b₄²)/4` is a legal substitution, and `field_simp` is
available.  See the module docstring for the measured size of the difference. -/
theorem hasPreΩSq_of_forall_hasPreΩSqAt_charZero {n : ℤ}
    (h : ∀ (F : Type) [Field F] [CharZero F] (V : WeierstrassCurve F) (x : F),
      V.HasPreΩSqAt n x)
    (W : WeierstrassCurve R) : W.HasPreΩSq n :=
  hasPreΩSq_of_forall_charZero
    (fun F _ _ V => hasPreΩSq_of_forall_hasPreΩSqAt (h F V)) W

/-! ### The polynomial identity at `n = 3` -/

/-- **`HasPreΩSq 3`, for every Weierstrass curve over every commutative ring.**  The input is
`WeierstrassCurve.Affine.hasPreΩSqAt_three`, which is the evaluated identity over a field of
characteristic `≠ 2`; the conclusion needs no hypothesis on the base at all.

⚠️ This adds **no algebra**.  Every monomial of the identity was already checked by
`hasPreΩSqAt_three`; what the reduction supplies is the right to have checked it with `4`
invertible.  `EllipticCurves.Torsion.OmegaOnCurve`'s module docstring measures the alternative at
9903 monomials and records that `lake build` killed it with exit `137`. -/
theorem hasPreΩSq_three (W : WeierstrassCurve R) : W.HasPreΩSq 3 :=
  hasPreΩSq_of_forall_hasPreΩSqAt_charZero
    (fun _ _ _ V x => Affine.hasPreΩSqAt_three (W := V.toAffine) two_ne_zero x) W

/-! ### Non-vacuity

⚠️ **Certificates, not content.**  Both are instances of `hasPreΩSq_three` and neither may be
cited; they exist so that a reduction which silently failed to escape its input's hypotheses would
break the build. -/

/-- **The certificate that matters: characteristic `2`.**  The input
`WeierstrassCurve.Affine.hasPreΩSqAt_three` requires `(2 : F) ≠ 0`, and `hasPreΩSq_three` holds
over `ZMod 2`, where `2 = 0`.  ⚠️ Do not cite this; use `hasPreΩSq_three`. -/
theorem hasPreΩSq_three_zmod_two (W : WeierstrassCurve (ZMod 2)) : W.HasPreΩSq 3 :=
  hasPreΩSq_three W

/-- **The certificate over `ℤ`**, the base for which `EllipticCurves.Torsion.OmegaOnCurve`'s
docstring states the identity is true but out of reach by `ring1`.  ⚠️ Do not cite this; use
`hasPreΩSq_three`. -/
theorem hasPreΩSq_three_int (W : WeierstrassCurve ℤ) : W.HasPreΩSq 3 :=
  hasPreΩSq_three W

end WeierstrassCurve
