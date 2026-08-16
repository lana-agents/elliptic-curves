/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairing

/-!
# The alternating property `e_n(T, T) = 1` — the reduction (Weil-pairing rung 6)

For the divisor-theoretic Weil-pairing element `e_n(S, T) := τ_T∗(g_S) / g_S ∈ F(W)`
(`weilPairingElt`, issue #419) the third named structural property (Silverman AEC III.8.1(d)) is
that it is **alternating**:

```
weilPairingElt_self : e_n(T, T) = 1.
```

Here the two arguments coincide: the divisor-slot function is `g_T` (the rung-5 `n`-th root attached
to `T`) and the translation is `τ_T∗ = translateEndo h_T` for the *same* point `T`.  Written out,
`e_n(T, T) = τ_T∗(g_T) / g_T`, so the claim is *exactly* that translation by `T` fixes `g_T` on the
nose:

```
τ_T∗ g_T = g_T   ⟺   e_n(T, T) = 1.
```

This file delivers the **Ward- and normality-independent reduction** of the alternating property to
that single translation-invariance fact:

* `weilPairingElt_eq_one_iff_translateEndo_fixed` — the clean characterisation
  `e_n(T, T) = 1 ↔ τ_T∗ g_T = g_T` (for `g_T ≠ 0`);
* `weilPairingElt_self_of_translateEndo_fixed`     — its forward direction, the reduction
  `τ_T∗ g_T = g_T ⟹ e_n(T, T) = 1`.

## Why the remaining content is genuinely gated

Being an `n`-th root of unity — `e_n(T, T) ^ n = 1`, already available from
`weilPairingElt_pow_eq_one` (#156) — is *not* enough to force `e_n(T, T) = 1`.  Pinning the ratio to
exactly `1` is the classical **product-over-`⟨T⟩` / divisor-telescoping** argument: with
`div g_T = [n]∗(T)` (rung 5, #418) and `[n]T = O`, the function `h := ∏_{i=0}^{n-1} τ_{[i]T}∗ g_T`
has `div h = 0` — because `T` is `n`-torsion, the multisets `{(1 − i)T}` and `{−iT}` are both all of
`⟨T⟩` — so `h` is a nonzero constant, and its translation-invariance forces `τ_T∗ g_T = g_T`.

That discharge of the `htinv : τ_T∗ g_T = g_T` hypothesis is the substantial, gated part of the
alternating property (issue #465, deliverable 2): it runs on the divisor / order-of-vanishing
calculus of `F(W)` (conditional on `IsDedekindDomain W.CoordinateRing`, #396), the rung-5 divisor
identity `div g_T = [n]∗(T)` (#418, rung-4 gated), and a divisor-pullback-under-translation
formula not yet in `FunctionField/`.  This file supplies the ungated scaffolding it will plug into.

## Out of scope

* **Discharging `τ_T∗ g_T = g_T`** — the product-over-`⟨T⟩` argument (#465 deliverable 2), gated as
  above.
* **Antisymmetry `e_n(T, S) = e_n(S, T)⁻¹`** — expands `e_n(S ⊕ T, S ⊕ T) = 1` via bilinearity in
  *both* slots, but only the translation slot is merged (`WeilPairingBilinear.lean`); the divisor
  slot is rung-4 gated (`g_{S ⊕ S'} = g_S · g_{S'}` up to a constant).
* **Non-degeneracy** — Ward-gated (#242).

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.
-/

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-- **The alternating property is exactly translation-invariance of `g_T`.**  For `g_T ≠ 0` the
Weil-pairing element `e_n(T, T) = τ_T∗(g_T) / g_T` equals `1` if and only if the translation `τ_T∗`
fixes `g_T`:

```
weilPairingElt h₂ g = 1 ↔ translateEndo h₂ g = g.
```

This is the Ward- and normality-independent reduction of the alternating property to the single
geometric fact `τ_T∗ g_T = g_T`; the latter is discharged by the product-over-`⟨T⟩` /
divisor-telescoping argument (#465 deliverable 2), which is gated on the divisor calculus. -/
theorem weilPairingElt_eq_one_iff_translateEndo_fixed {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    {g : W.FunctionField} (hg : g ≠ 0) :
    weilPairingElt h₂ g = 1 ↔ translateEndo h₂ g = g := by
  rw [weilPairingElt, div_eq_iff hg, one_mul]

/-- **The alternating property from translation-invariance (`e_n(T, T) = 1`).**  If the translation
`τ_T∗` fixes the rung-5 root `g_T` (`htinv : translateEndo h₂ g = g`), then the Weil-pairing element
`e_n(T, T) = τ_T∗(g_T) / g_T = g_T / g_T = 1`.

The forward direction of `weilPairingElt_eq_one_iff_translateEndo_fixed`; the hypothesis `htinv` is
the single genuinely-gated input, to be discharged by the product-over-`⟨T⟩` argument
(#465 deliverable 2). -/
theorem weilPairingElt_self_of_translateEndo_fixed {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    {g : W.FunctionField} (hg : g ≠ 0) (htinv : translateEndo h₂ g = g) :
    weilPairingElt h₂ g = 1 :=
  (weilPairingElt_eq_one_iff_translateEndo_fixed h₂ hg).mpr htinv

end CoordinateRing

end WeierstrassCurve.Affine
