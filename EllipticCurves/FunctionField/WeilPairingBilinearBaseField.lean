/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.TranslationTorsionMap
import EllipticCurves.FunctionField.WeilPairingConstant

/-!
# Translation-slot bilinearity of `e_n` from a base-field group relation (rung 6)

Let `W` be an elliptic curve over a field `F`.  The translation-slot bilinearity of the
Weil-pairing element (`WeilPairing.lean`, issue #419)

```
e_n(S, T) := weilPairingElt h₂ g = τ_T∗(g) / g,   τ_T∗ = translateEndo h₂ : F(W) →+* F(W),
```

is already delivered — unconditionally in `e_n`-constancy — as
`weilPairingElt_translatePoint_add_of_algClosed` (`WeilPairingConstant.lean`, #419): for affine
points `T_P, T_Q, T_R` on `W` satisfying the group relation `𝒯_P + 𝒯_Q = 𝒯_R` **over `F(W)`**
(`hsum`) it gives `e_n(S, T_R) = e_n(S, T_P) · e_n(S, T_Q)`.

The one input still carried as a *function-field* hypothesis there is `hsum`.  This file discharges
it from an honest **base-field** group-law relation `P ⊕ Q = R` in `W.Point`, closing the follow-on
that PR #160's review (issue #432) flagged: *"discharging `hsum` from an `F`-level point sum
(mechanical base-change transport)."*

## The route — the base-change point homomorphism

`translatePoint hP` is the image of the base-field point `torsionPoint hP = (x_P, y_P)` under the
base-change group homomorphism `torsionPointMap = Point.map (Algebra.ofId F F(W))`
(`torsionPointMap_torsionPoint`, `TranslationTorsionMap.lean`, #444).  Being an `AddMonoidHom`, it
sends the base-field relation `P ⊕ Q = R` to the `F(W)`-level relation `𝒯_P + 𝒯_Q = 𝒯_R`.  This is
the *additive* mirror of the merged `translatePoint_nsmul_eq_zero` (which transports `n • T = 0`).
Note `torsionPoint` is `.some x y _` for **any** equation point — the name is a slight misnomer, it
is not restricted to torsion — so the transport applies to general `P, Q, R`.

## Main results

* `translatePoint_add` — the general-addition transport `P ⊕ Q = R ⟹ 𝒯_P + 𝒯_Q = 𝒯_R`;
* `weilPairingElt_translatePoint_add_of_baseField` — translation-slot bilinearity consuming only the
  base-field relation `torsionPoint hP + torsionPoint hQ = torsionPoint hR` (plus `g ≠ 0`, `n ≠ 0`,
  and the root-of-unity datum `e_n(S, T_Q) ^ n = 1`).

## Scope

Ward- and normality-independent: needs only `[Field F] [W.IsElliptic]`.  Bilinearity in the divisor
slot `S` is merged, on exactly those hypotheses, as `WeilPairingAntisymmetric` (#723), together
with the antisymmetry corollary `e_n(T, S) = e_n(S, T)⁻¹`; what stays gated on rung 4/5 there is
only the *production* of `g_{S ⊕ S'} = g_S · g_{S'} · w`, carried as the hypothesis `hprod` in the
same style as `hfix` and `hsum` here.  Alternating (`e_n(S, S) = 1`) and Galois-equivariance are
separate #419 sub-items; non-degeneracy is Ward-gated (#242).

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.
-/

open Polynomial

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

open Classical in
/-- **General-addition transport of translation points.**  If the base-field points
`P = (x_P, y_P)`, `Q = (x_Q, y_Q)`, `R = (x_R, y_R)` satisfy the group relation `P ⊕ Q = R` in
`W.Point` (`hadd`, stated on `torsionPoint`), then their constant base changes satisfy
`𝒯_P + 𝒯_Q = 𝒯_R` in `(W ⁄ F(W)).Point`.

Immediate from the base-change homomorphism `torsionPointMap` (which sends `torsionPoint` to
`translatePoint`, `torsionPointMap_torsionPoint`) being an `AddMonoidHom`: rewrite each
`translatePoint` as `torsionPointMap (torsionPoint _)`, collapse the sum with `← map_add`, and close
with `hadd`.  The additive mirror of `translatePoint_nsmul_eq_zero`. -/
theorem translatePoint_add {xP yP xQ yQ xR yR : F}
    (hP : W.Equation xP yP) (hQ : W.Equation xQ yQ) (hR : W.Equation xR yR)
    (hadd : torsionPoint hP + torsionPoint hQ = torsionPoint hR) :
    translatePoint hP + translatePoint hQ = translatePoint hR := by
  rw [← torsionPointMap_torsionPoint hP, ← torsionPointMap_torsionPoint hQ,
    ← torsionPointMap_torsionPoint hR, ← map_add, hadd]

open Classical in
/-- **Translation-slot bilinearity of the Weil-pairing element from a base-field group relation.**
For affine points `T_P, T_Q, T_R` on `W` satisfying `T_P ⊕ T_Q = T_R` in `W.Point` (`hadd`), a
nonzero `g`, and the root-of-unity datum `e_n(S, T_Q) ^ n = 1` (`hpow`, `n ≠ 0`),

```
e_n(S, T_R) = e_n(S, T_P) · e_n(S, T_Q).
```

Composes the base-change transport `translatePoint_add` (turning the base-field relation into the
`F(W)`-level `hsum`) with `weilPairingElt_translatePoint_add_of_algClosed`
(`WeilPairingConstant.lean`), whose constancy of `e_n(S, T_Q)` is discharged internally via
geometric integrality.  No residual function-field hypothesis remains beyond the root-of-unity
datum. -/
theorem weilPairingElt_translatePoint_add_of_baseField
    {xP yP xQ yQ xR yR : F} (hP : W.Equation xP yP) (hQ : W.Equation xQ yQ)
    (hR : W.Equation xR yR)
    (hadd : torsionPoint hP + torsionPoint hQ = torsionPoint hR)
    {g : W.FunctionField} (hg : g ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hpow : weilPairingElt hQ g ^ n = 1) :
    weilPairingElt hR g = weilPairingElt hP g * weilPairingElt hQ g :=
  weilPairingElt_translatePoint_add_of_algClosed hP hQ hR
    (translatePoint_add hP hQ hR hadd) hg hn hpow

end CoordinateRing

end WeierstrassCurve.Affine
