/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByTwoEndomorphism
import EllipticCurves.FunctionField.MulByThreeEndomorphism

/-!
# The Weil-pairing element `e_n(S, T)` (Weil-pairing construction, rung 6)

Let `W` be a Weierstrass curve over a field `F` whose affine coordinate ring `F[W]` is a Dedekind
domain.  The divisor-theoretic Weil pairing (Silverman AEC III.8) is built from the `n`-th root
`g_S ∈ F(W)` of the pulled-back principal function of a nonzero `n`-torsion point `S` (rung 5,
issue #418): a nonzero `g_S` with

```
u · g_S ^ n = [n]∗ f_S   (u a unit of F[W], [n]∗ = mulByTwoEndo the multiplication-by-n pullback).
```

For a second `n`-torsion point `T = (x₂, y₂)` with translation endomorphism
`τ_T∗ = translateEndo h₂ : F(W) →+* F(W)` (issue #406), the pairing value is the ratio

```
e_n(S, T) := τ_T∗(g_S) / g_S ∈ F(W).
```

This file defines that element (`weilPairingElt`) and proves its defining property — that it is an
`n`-th root of unity, `e_n(S, T) ^ n = 1` — reduced to the single algebraic fact that the
translation fixes `g_S ^ n`:

* `weilPairingElt`               — the element `τ_T∗(g_S) / g_S`;
* `weilPairingElt_ne_zero`       — it is nonzero (for `g_S ≠ 0`);
* `weilPairingElt_pow_eq_one`    — `e_n(S, T) ^ n = 1` from `translateEndo h₂ (g_S ^ n) = g_S ^ n`.

## Why `τ_T∗` fixes `g_S ^ n`, and the scope delivered here

The reason `τ_T∗` fixes `g_S ^ n` is the geometric identity `[n](P + T) = [n]P` (valid because
`T` is an `n`-torsion point, `[n]T = O`): pulling `[n]∗ f_S = u · g_S ^ n` back by `τ_T` leaves it
unchanged, so `τ_T∗(u · g_S ^ n) = u · g_S ^ n`.  Cancelling the unit `u` (which `τ_T∗` also fixes,
being a nonzero constant of `F[W]`) yields `τ_T∗(g_S ^ n) = g_S ^ n`.

This file therefore packages the **Ward- and normality-independent algebra** of rung 6: the
definition of `e_n(S, T)`, its non-vanishing, and the `μ_n`-membership `e_n ^ n = 1`, reduced via
`translateEndo_pow_eq_self_of` to exactly two named inputs on the concrete `n = 2`/`n = 3` data —

* `hcomm : translateEndo h₂ ([n]∗ f_S) = [n]∗ f_S` (the `[n](P + T) = [n]P` commuting identity),
* `huf`   : `translateEndo h₂` fixes the unit `u`  (the unit `u` of `F[W]` is a constant),

both of which are genuine rational-function identities carried here as hypotheses, to be discharged
by a follow-on.  Everything else — the definition, non-vanishing, the `n`-th-root-of-unity property,
and the cancellation reducing the two inputs to `τ_T∗(g_S ^ n) = g_S ^ n` — is unconditional.

## Explicitly out of scope (as issue #419 records)

* **Bilinearity, alternating, Galois-equivariance** — separately valuable follow-ons.
* **Non-degeneracy** — needs `#E[n] = n²` (#242), Ward-gated.
* **General `n`** — needs the general `[n]∗` (#404 crux); only `n = 2, 3` are concretely available.
* The normality discharge `IsIntegrallyClosed W.CoordinateRing` (#396 Part A) — research-blocked;
  Dedekindness is carried as a hypothesis throughout `FunctionField/`.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.
-/

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-- **The Weil-pairing element** `e_n(S, T) := τ_T∗(g_S) / g_S ∈ F(W)`.

Here `g = g_S` is the `n`-th root of the pulled-back principal function of `S` (rung 5) and
`h₂ : W.Equation x₂ y₂` encodes the translation point `T = (x₂, y₂)` via `translateEndo h₂`. -/
noncomputable def weilPairingElt {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) (g : W.FunctionField) :
    W.FunctionField :=
  translateEndo h₂ g / g

/-- The Weil-pairing element is nonzero whenever `g_S` is (the translation endomorphism is
injective, so `τ_T∗(g_S) ≠ 0`, and the quotient of two nonzero elements is nonzero). -/
theorem weilPairingElt_ne_zero {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {g : W.FunctionField}
    (hg : g ≠ 0) : weilPairingElt h₂ g ≠ 0 := by
  have hinj : Function.Injective (translateEndo h₂) := RingHom.injective _
  rw [weilPairingElt]
  exact div_ne_zero ((map_ne_zero_iff _ hinj).mpr hg) hg

/-- **`e_n(S, T)` is an `n`-th root of unity.** Given that the translation fixes `g_S ^ n`
(`translateEndo h₂ (g ^ n) = g ^ n`), the pairing value satisfies `e_n(S, T) ^ n = 1`:
`(τ_T∗ g / g) ^ n = τ_T∗(g ^ n) / g ^ n = g ^ n / g ^ n = 1`. -/
theorem weilPairingElt_pow_eq_one {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {g : W.FunctionField}
    (hg : g ≠ 0) {n : ℕ} (hfix : translateEndo h₂ (g ^ n) = g ^ n) :
    weilPairingElt h₂ g ^ n = 1 := by
  rw [weilPairingElt, div_pow, ← map_pow, hfix, div_self (pow_ne_zero n hg)]

/-- **The translation fixes `g_S ^ n`.** From the rung-5 datum `u · g ^ n = h` (with `h = [n]∗ f_S`
the pulled-back principal function and `u` a unit of `F[W]`), together with the two inputs

* `hcomm : translateEndo h₂ h = h` — the commuting identity `[n](P + T) = [n]P`, and
* `huf`   : the translation fixes the constant unit `u`,

the translation fixes `g ^ n`.  Applying `translateEndo h₂` to `u · g ^ n = h` and cancelling the
nonzero factor `algebraMap u` gives `translateEndo h₂ (g ^ n) = g ^ n`. -/
theorem translateEndo_pow_eq_self_of {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    {g h : W.FunctionField} {u : W.CoordinateRingˣ} {n : ℕ}
    (hu : (u : W.CoordinateRing) • g ^ n = h)
    (hcomm : translateEndo h₂ h = h)
    (huf : translateEndo h₂ (algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing))
      = algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing)) :
    translateEndo h₂ (g ^ n) = g ^ n := by
  have hsmul : algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing) * g ^ n = h := by
    rw [← Algebra.smul_def]; exact hu
  have hA : algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective W.CoordinateRing W.FunctionField)]
    exact u.ne_zero
  have key : algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing) *
      translateEndo h₂ (g ^ n) =
      algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing) * g ^ n := by
    have hcong := congrArg (translateEndo h₂) hsmul
    rw [map_mul, huf, hcomm] at hcong
    exact hcong.trans hsmul.symm
  exact mul_left_cancel₀ hA key

/-- **`e_n(S, T) ^ n = 1` from the rung-5 datum and the two named inputs.** Combines
`translateEndo_pow_eq_self_of` (which produces `translateEndo h₂ (g ^ n) = g ^ n`) with
`weilPairingElt_pow_eq_one`.  Here `h = [n]∗ f_S = mulByTwoEndo h2 f` and `g = g_S`. -/
theorem weilPairingElt_pow_eq_one_of_gS {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) (h2 : (2 : F) ≠ 0)
    {f g : W.FunctionField} {u : W.CoordinateRingˣ} {n : ℕ} (hg : g ≠ 0)
    (hu : (u : W.CoordinateRing) • g ^ n = mulByTwoEndo h2 f)
    (hcomm : translateEndo h₂ (mulByTwoEndo h2 f) = mulByTwoEndo h2 f)
    (huf : translateEndo h₂ (algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing))
      = algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing)) :
    weilPairingElt h₂ g ^ n = 1 :=
  weilPairingElt_pow_eq_one h₂ hg (translateEndo_pow_eq_self_of h₂ hu hcomm huf)

/-- **`e_n(S, T) ^ n = 1`, concrete `n = 3` instance.** The `mulByThreeEndo` analogue of
`weilPairingElt_pow_eq_one_of_gS`: here the pulled-back principal function is
`h = [3]∗ f_S = mulByThreeEndo h2 h3 f` and `g = g_S` is the rung-5 `n = 3` root
(`exists_gS_three`, `u · g ^ 3 = mulByThreeEndo h2 h3 f`).  Nothing in the reduction is specific to
`n = 2`: `translateEndo_pow_eq_self_of` and `weilPairingElt_pow_eq_one` are `n`-agnostic, so the two
named inputs `hcomm`/`huf` are supplied on the `mulByThreeEndo` datum and the same cancellation
produces `e_n(S, T) ^ n = 1`. -/
theorem weilPairingElt_pow_eq_one_of_gS_three {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {f g : W.FunctionField} {u : W.CoordinateRingˣ} {n : ℕ} (hg : g ≠ 0)
    (hu : (u : W.CoordinateRing) • g ^ n = mulByThreeEndo h2 h3 f)
    (hcomm : translateEndo h₂ (mulByThreeEndo h2 h3 f) = mulByThreeEndo h2 h3 f)
    (huf : translateEndo h₂ (algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing))
      = algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing)) :
    weilPairingElt h₂ g ^ n = 1 :=
  weilPairingElt_pow_eq_one h₂ hg (translateEndo_pow_eq_self_of h₂ hu hcomm huf)

end CoordinateRing

end WeierstrassCurve.Affine
