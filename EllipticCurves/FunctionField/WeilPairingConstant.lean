/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.ConstantFieldDomain
import EllipticCurves.FunctionField.WeilPairing
import EllipticCurves.FunctionField.WeilPairingBilinear

/-!
# The Weil-pairing element is a constant, and unconditional bilinearity from it (rung 6)

Let `W` be an elliptic curve over a field `F`.  The Weil-pairing element
(`WeilPairing.lean`, issue #419)

```
e_n(S, T) := weilPairingElt h₂ g = τ_T∗(g) / g,   τ_T∗ = translateEndo h₂ : F(W) →+* F(W),
```

is already known to be an `n`-th root of unity: `e_n(S, T) ^ n = 1`
(`weilPairingElt_pow_eq_one`, and its concrete `n = 2 / n = 3` combined forms
`weilPairingElt_pow_eq_one_of_gS' / _three'`).

This file discharges the **`e_n`-is-a-constant** gate of rung 6 — the fact that upgrades the
conditional translation-slot bilinearity `weilPairingElt_translatePoint_add_of_const`
(`WeilPairingBilinear.lean`, issue #419) to an unconditional statement — along a route that
**avoids `IsIntegrallyClosed W.CoordinateRing`** entirely — and still does, for a reason that has
outlived the one first given here: that hypothesis is no longer a wall (it is a global instance for
`[W.IsElliptic]`, `EllipticCurves.FunctionField.CoordinateRingNormalGeneral`), but this route does
not need `[W.IsElliptic]` either, so it remains the more general of the two.

## The route — the constant field, not the divisor

The observation is elementary once `e_n(S, T) ^ n = 1` is in hand: a root of unity is **algebraic
over `F`**, so it lies in the *relative algebraic closure* `K := algebraicClosure F F(W)` (the
constant field of `F(W)`).  Hence, the moment one knows `K = ⊥` — i.e. that `F` is relatively
algebraically closed in its function field `F(W)`, equivalently that `F` is the full field of
constants — the pairing value is forced to be a genuine constant `algebraMap F F(W) c`.

`K = ⊥` is the *geometric integrality* of the Weierstrass curve, now available **unconditionally**
as `algebraicClosure_functionField_eq_bot` (`ConstantFieldDomain.lean`, #434): the base change of
`F(W)` to `AlgebraicClosure F` is a domain (the Weierstrass polynomial stays irreducible over the
algebraic closure), so `F` is relatively algebraically closed in `F(W)`.  Feeding that theorem here
makes the constancy of `e_n(S, T)` and the translation-slot bilinearity hold for `[Field F]` alone,
with no residual constant-field hypothesis.  This is a **different** unlock from both the normality
route (`F[W]` integrally closed in `F(W)`) and the divisor-pullback route (translation-invariance of
`div g_S`, gated on rung 4) — either of which would also deliver constancy, but both are heavier
here: the first now costs `[W.IsElliptic]`, which this file does not assume, and the second is
still rung-4 gated.

## Main results

* `exists_algebraMap_of_pow_eq_one` — any `z ∈ F(W)` with `z ^ n = 1` (`n ≠ 0`) is a constant
  `algebraMap F F(W) c`, unconditionally;
* `weilPairingElt_isConstant` / `_of_gS'` / `_of_gS_three'` — the pairing value `e_n(S, T)` is such
  a constant, from `e_n(S, T) ^ n = 1`;
* `weilPairingElt_isRootOfUnity` / `_of_gS'` / `_of_gS_three'` — the sharper **μ_n-membership**: the
  base-field constant `c` with `e_n(S, T) = algebraMap F F(W) c` is itself an `n`-th root of unity,
  `c ^ n = 1` in `F` — i.e. `e_n(S, T) ∈ μ_n(F)`, the value group issue #419 names;
* `weilPairingElt_translatePoint_add_of_algClosed` — **unconditional** (modulo the group
  relation `hsum`) bilinearity in the translation slot, obtained by feeding constancy to
  `weilPairingElt_translatePoint_add_of_const`.

## Scope

Ward- and normality-independent: needs only `[Field F] [W.IsElliptic]` and the root-of-unity input
(already delivered).  The constant-field fact is discharged internally via
`algebraicClosure_functionField_eq_bot`.  Non-degeneracy remains out of scope, and it is **not**
Ward-gated — `WeilPairing`'s scope section is the canonical account of what it consumes (#769).

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.
-/

open Polynomial

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

/-- A root of unity in the function field is a **constant**.  Indeed `z ^ n = 1` makes `z` algebraic
over `F`, hence a member of the relative algebraic closure `algebraicClosure F F(W)`, which the
geometric-integrality theorem `algebraicClosure_functionField_eq_bot` identifies with `⊥`, i.e. the
image of `F`. -/
theorem exists_algebraMap_of_pow_eq_one {z : W.FunctionField} {n : ℕ} (hn : n ≠ 0)
    (hz : z ^ n = 1) :
    ∃ c : F, z = algebraMap F W.FunctionField c := by
  -- `z` is algebraic over `F`: it is a root of the nonzero polynomial `X ^ n - 1`.
  have halgz : IsAlgebraic F z :=
    ⟨X ^ n - C 1, (monic_X_pow_sub_C (1 : F) hn).ne_zero, by
      rw [map_sub, map_pow, aeval_X, aeval_C, map_one, hz, sub_self]⟩
  -- hence `z` lies in the relative algebraic closure, pinned to `⊥ = image of F` by geometric
  -- integrality of the Weierstrass curve.
  have hmem : z ∈ algebraicClosure F W.FunctionField := mem_algebraicClosure_iff.mpr halgz
  rw [W.algebraicClosure_functionField_eq_bot, IntermediateField.mem_bot] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc.symm⟩

/-- **The Weil-pairing element is a constant.**  From `e_n(S, T) ^ n = 1` (`n ≠ 0`) the value
`e_n(S, T)` equals a genuine constant `algebraMap F F(W) c`. -/
theorem weilPairingElt_isConstant [W.IsElliptic] {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    {g : W.FunctionField} {n : ℕ} (hn : n ≠ 0) (hpow : weilPairingElt h₂ g ^ n = 1) :
    ∃ c : F, weilPairingElt h₂ g = algebraMap F W.FunctionField c :=
  exists_algebraMap_of_pow_eq_one hn hpow

/-- **The `n = 2`-track Weil-pairing element is a constant.**  Specialises
`weilPairingElt_isConstant` to the concrete combined datum `weilPairingElt_pow_eq_one_of_gS'`, which
supplies `e_n(S, T) ^ n = 1` from a coordinate-ring unit relation `u • g ^ n = mulByTwoEndo h2 f`
and the translation-commuting `hcomm`. -/
theorem weilPairingElt_isConstant_of_gS' [W.IsElliptic] {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    (h2 : (2 : F) ≠ 0) {f g : W.FunctionField} {u : W.CoordinateRingˣ} {n : ℕ} (hn : n ≠ 0)
    (hg : g ≠ 0) (hu : (u : W.CoordinateRing) • g ^ n = mulByTwoEndo h2 f)
    (hcomm : translateEndo h₂ (mulByTwoEndo h2 f) = mulByTwoEndo h2 f) :
    ∃ c : F, weilPairingElt h₂ g = algebraMap F W.FunctionField c :=
  weilPairingElt_isConstant h₂ hn (weilPairingElt_pow_eq_one_of_gS' h₂ h2 hg hu hcomm)

/-- **The `n = 3`-track Weil-pairing element is a constant.**  The `mulByThreeEndo` mirror of
`weilPairingElt_isConstant_of_gS'`, over the concrete datum
`weilPairingElt_pow_eq_one_of_gS_three'`. -/
theorem weilPairingElt_isConstant_of_gS_three' [W.IsElliptic] {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {f g : W.FunctionField} {u : W.CoordinateRingˣ} {n : ℕ}
    (hn : n ≠ 0) (hg : g ≠ 0) (hu : (u : W.CoordinateRing) • g ^ n = mulByThreeEndo h2 h3 f)
    (hcomm : translateEndo h₂ (mulByThreeEndo h2 h3 f) = mulByThreeEndo h2 h3 f) :
    ∃ c : F, weilPairingElt h₂ g = algebraMap F W.FunctionField c :=
  weilPairingElt_isConstant h₂ hn (weilPairingElt_pow_eq_one_of_gS_three' h₂ h2 h3 hg hu hcomm)

/-- **Unconditional bilinearity of the Weil-pairing element in the translation slot.**  For affine
points `T_P, T_Q, T_R` with `T_P ⊕ T_Q = T_R` (`hsum`), a nonzero `g`, and given that the pairing
value `e_n(S, T_Q) ^ n = 1` (`hpow`), the constancy of `e_n(S, T_Q)` (from
`weilPairingElt_isConstant`) discharges the `hfix` input of
`weilPairingElt_translatePoint_add_of_const`, giving

```
e_n(S, T_R) = e_n(S, T_P) · e_n(S, T_Q)
```

with no residual `hfix`/`hconst`/constant-field hypothesis beyond `hpow` and the group relation. -/
theorem weilPairingElt_translatePoint_add_of_algClosed [W.IsElliptic]
    {xP yP xQ yQ xR yR : F} (hP : W.Equation xP yP) (hQ : W.Equation xQ yQ)
    (hR : W.Equation xR yR)
    (hsum : translatePoint hP + translatePoint hQ = translatePoint hR)
    {g : W.FunctionField} (hg : g ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hpow : weilPairingElt hQ g ^ n = 1) :
    weilPairingElt hR g = weilPairingElt hP g * weilPairingElt hQ g := by
  obtain ⟨c, hc⟩ := weilPairingElt_isConstant hQ hn hpow
  exact weilPairingElt_translatePoint_add_of_const hP hQ hR hsum hg hc

/-- **The Weil-pairing element lands in `μ_n(F)`.**  From `e_n(S, T) ^ n = 1` (`n ≠ 0`), not only is
`e_n(S, T)` a constant `algebraMap F F(W) c` (`weilPairingElt_isConstant`), but the base-field
constant `c` is itself an `n`-th root of unity: `c ^ n = 1` in `F`.  Indeed, applying the injective
`algebraMap F F(W)` to `c ^ n = 1` is the same as `(algebraMap F F(W) c) ^ n = e_n(S, T) ^ n = 1`.
This packages the μ_n-membership that issue #419 names for the pairing value, pulled back from
`F(W)` down to the base field. -/
theorem weilPairingElt_isRootOfUnity [W.IsElliptic] {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    {g : W.FunctionField} {n : ℕ} (hn : n ≠ 0) (hpow : weilPairingElt h₂ g ^ n = 1) :
    ∃ c : F, weilPairingElt h₂ g = algebraMap F W.FunctionField c ∧ c ^ n = 1 := by
  obtain ⟨c, hc⟩ := weilPairingElt_isConstant h₂ hn hpow
  refine ⟨c, hc, (algebraMap F W.FunctionField).injective ?_⟩
  rw [map_pow, ← hc, hpow, map_one]

/-- **The `n = 2`-track Weil-pairing element lands in `μ_n(F)`.**  Specialises
`weilPairingElt_isRootOfUnity` to the concrete combined datum `weilPairingElt_pow_eq_one_of_gS'`,
mirroring `weilPairingElt_isConstant_of_gS'`. -/
theorem weilPairingElt_isRootOfUnity_of_gS' [W.IsElliptic] {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    (h2 : (2 : F) ≠ 0) {f g : W.FunctionField} {u : W.CoordinateRingˣ} {n : ℕ} (hn : n ≠ 0)
    (hg : g ≠ 0) (hu : (u : W.CoordinateRing) • g ^ n = mulByTwoEndo h2 f)
    (hcomm : translateEndo h₂ (mulByTwoEndo h2 f) = mulByTwoEndo h2 f) :
    ∃ c : F, weilPairingElt h₂ g = algebraMap F W.FunctionField c ∧ c ^ n = 1 :=
  weilPairingElt_isRootOfUnity h₂ hn (weilPairingElt_pow_eq_one_of_gS' h₂ h2 hg hu hcomm)

/-- **The `n = 3`-track Weil-pairing element lands in `μ_n(F)`.**  The `mulByThreeEndo` mirror of
`weilPairingElt_isRootOfUnity_of_gS'`, over the concrete datum
`weilPairingElt_pow_eq_one_of_gS_three'`. -/
theorem weilPairingElt_isRootOfUnity_of_gS_three' [W.IsElliptic] {x₂ y₂ : F}
    (h₂ : W.Equation x₂ y₂) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {f g : W.FunctionField}
    {u : W.CoordinateRingˣ} {n : ℕ} (hn : n ≠ 0) (hg : g ≠ 0)
    (hu : (u : W.CoordinateRing) • g ^ n = mulByThreeEndo h2 h3 f)
    (hcomm : translateEndo h₂ (mulByThreeEndo h2 h3 f) = mulByThreeEndo h2 h3 f) :
    ∃ c : F, weilPairingElt h₂ g = algebraMap F W.FunctionField c ∧ c ^ n = 1 :=
  weilPairingElt_isRootOfUnity h₂ hn (weilPairingElt_pow_eq_one_of_gS_three' h₂ h2 h3 hg hu hcomm)

end CoordinateRing

end WeierstrassCurve.Affine
