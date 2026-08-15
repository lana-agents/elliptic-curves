/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.TranslationComposition
import EllipticCurves.FunctionField.WeilPairing

/-!
# Bilinearity of the Weil-pairing element in the translation slot (rung 6)

Let `W` be an elliptic curve over a field `F`.  For a fixed `n`-torsion point `S` with `n`-th root
`g = g_S ∈ F(W)` (rung 5, issue #418) and a translation point `T = (x₂, y₂)`, the Weil-pairing
element (`WeilPairing.lean`, issue #419) is

```
e_n(S, T) := weilPairingElt h₂ g = τ_T∗(g) / g,   τ_T∗ = translateEndo h₂ : F(W) →+* F(W).
```

This file proves **bilinearity in the translation slot `T`**: for affine points `T_P`, `T_Q`, `T_R`
with `T_P ⊕ T_Q = T_R` in the group `(W ⁄ F(W)).Point`,

```
e_n(S, T_R) = e_n(S, T_P) · e_n(S, T_Q).
```

* `weilPairingElt_translatePoint_add`      — the bilinearity identity from the explicit hypothesis
  `hfix : τ_{T_P}∗(e_n(S, T_Q)) = e_n(S, T_Q)` (translation fixes the pairing value);
* `weilPairingElt_translatePoint_add_of_const` — the same conclusion when `e_n(S, T_Q)` is a
  constant `algebraMap F F(W) c`, which makes `hfix` automatic (`translateEndo_algebraMap_base`).

## The keystone consumed and the one input carried

The engine is the **composition law** `τ_{T_P}∗ ∘ τ_{T_Q}∗ = τ_{T_R}∗`
(`translateEndo_translateEndo_apply`, `FunctionField/TranslationComposition.lean`, issue #432),
the contravariant functoriality of the translation pullback with respect to the group law.  Writing
`τ_{T_Q}∗(g) = e_n(S, T_Q) · g` and pushing through `τ_{T_P}∗`,

```
e_n(S, T_R) = τ_{T_R}∗(g)/g = τ_{T_P}∗(τ_{T_Q}∗(g))/g
            = τ_{T_P}∗(e_n(S, T_Q)) · τ_{T_P}∗(g) / g
            = τ_{T_P}∗(e_n(S, T_Q)) · e_n(S, T_P).
```

This equals `e_n(S, T_Q) · e_n(S, T_P)` exactly when `τ_{T_P}∗` **fixes** the pairing value
`e_n(S, T_Q)`.  That is the genuine remaining geometric content — the pairing value is a *global
constant* (its divisor is `0`), whence fixed by every translation — and it is carried here as the
explicit hypothesis `hfix`, matching the conditional-partial methodology of the rest of rung 6
(`hcomm`, `huf`, `hprin`).  `weilPairingElt_translatePoint_add_of_const` records the clean special
case where the constancy is supplied as `e_n(S, T_Q) = algebraMap F F(W) c`.

## Scope

Ward- and normality-independent: needs only `[Field F] [W.IsElliptic]` and the group relation
`hsum` on the translation points.  Non-degeneracy remains out of scope (Ward-gated, #242); so is
bilinearity in the divisor slot `S` (needs `g_{S ⊕ S'} = g_S · g_{S'}` up to a constant, a
divisor-level statement gated on rung 4).

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.
-/

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-- **Bilinearity of the Weil-pairing element in the translation slot.**  For affine points `T_P`,
`T_Q`, `T_R` with `T_P ⊕ T_Q = T_R` (as the constant-point identity `𝒯_P + 𝒯_Q = 𝒯_R` over `F(W)`,
`hsum`), and given that the translation `τ_{T_P}∗` fixes the pairing value `e_n(S, T_Q)` (`hfix` —
which holds because the value is a global constant),

```
e_n(S, T_R) = e_n(S, T_P) · e_n(S, T_Q).
```

The proof reads `τ_{T_R}∗(g) = τ_{T_P}∗(τ_{T_Q}∗(g))` via the composition law
(`translateEndo_translateEndo_apply`, #432), writes `τ_{T_Q}∗(g) = e_n(S, T_Q) · g`, and pushes the
constant `e_n(S, T_Q)` through `τ_{T_P}∗` using `hfix`. -/
theorem weilPairingElt_translatePoint_add {xP yP xQ yQ xR yR : F}
    (hP : W.Equation xP yP) (hQ : W.Equation xQ yQ) (hR : W.Equation xR yR)
    (hsum : translatePoint hP + translatePoint hQ = translatePoint hR)
    {g : W.FunctionField} (hg : g ≠ 0)
    (hfix : translateEndo hP (weilPairingElt hQ g) = weilPairingElt hQ g) :
    weilPairingElt hR g = weilPairingElt hP g * weilPairingElt hQ g := by
  -- `τ_{T_Q}∗(g) = e_n(S, T_Q) · g`, straight from the definition of `e_n`.
  have hQg : translateEndo hQ g = weilPairingElt hQ g * g := by
    rw [weilPairingElt, div_mul_cancel₀ _ hg]
  -- The numerator identity `τ_{T_R}∗(g) = e_n(S, T_P) · e_n(S, T_Q) · g`.
  have key : translateEndo hR g = weilPairingElt hP g * weilPairingElt hQ g * g := by
    rw [← translateEndo_translateEndo_apply hP hQ hR hsum, hQg, map_mul, hfix]
    simp only [weilPairingElt]
    field_simp
  have hunfold : weilPairingElt hR g = translateEndo hR g / g := rfl
  rw [hunfold, key, mul_div_assoc, div_self hg, mul_one]

/-- **Bilinearity in the translation slot, constant form.**  If the pairing value `e_n(S, T_Q)` is a
nonzero constant `algebraMap F F(W) c` — the true state of affairs, as its divisor vanishes — then
the `hfix` hypothesis of `weilPairingElt_translatePoint_add` is automatic
(`translateEndo_algebraMap_base`: translations fix the base field), giving
`e_n(S, T_R) = e_n(S, T_P) · e_n(S, T_Q)` outright. -/
theorem weilPairingElt_translatePoint_add_of_const {xP yP xQ yQ xR yR : F}
    (hP : W.Equation xP yP) (hQ : W.Equation xQ yQ) (hR : W.Equation xR yR)
    (hsum : translatePoint hP + translatePoint hQ = translatePoint hR)
    {g : W.FunctionField} (hg : g ≠ 0) {c : F}
    (hconst : weilPairingElt hQ g = algebraMap F W.FunctionField c) :
    weilPairingElt hR g = weilPairingElt hP g * weilPairingElt hQ g :=
  weilPairingElt_translatePoint_add hP hQ hR hsum hg
    (by rw [hconst, translateEndo_algebraMap_base])

end CoordinateRing

end WeierstrassCurve.Affine
