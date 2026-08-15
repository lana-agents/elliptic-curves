/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.TranslationDoublingComm

/-!
# Transporting the `2`-torsion hypothesis of the `n = 2` Weil-pairing element to the base field

The `n = 2` `hcomm` discharge of `FunctionField/TranslationDoublingComm.lean` (#433) reads its
commuting hypothesis off a `2`-torsion relation *over the function field* `F(W)`:

```
htors : translatePoint hT + translatePoint hT = 0        -- in (W ⁄ F(W)).Point.
```

`translatePoint hT` is the constant point `T = (xT, yT)` — the fixed `F`-point base changed to
`F(W)`.  This file discharges `htors` from an **honest torsion fact about `T` over the base field
`F`**, so that the Weil-pairing element's `n`-th-root-of-unity property no longer mentions the
function field in its hypotheses:

* from the *on-curve* `2`-torsion condition `yT = W.negY xT yT` (the affine vertical-tangent
  characterisation of `[2]T = O`, `T ≠ O`), via `Point.add_self_of_Y_eq` and the naturality of
  `negY` under base change (`map_negY`);
* from the *group-theoretic* `2`-torsion relation `T + T = 0` in `W.Point` itself, via the general
  `add_eq_zero_iff_eq_neg` and `Point.neg_some`.

## Main results

* `torsionPoint` — the fixed `F`-point `T = (xT, yT)` as an element of `W.Point`;
* `negY_of_torsionPoint_add_self` — the group relation `T + T = 0` over `F` gives the on-curve
  condition `yT = W.negY xT yT`;
* `translatePoint_add_self_of_negY` — the on-curve `2`-torsion condition transports to
  `translatePoint hT + translatePoint hT = 0` over `F(W)`;
* `translatePoint_add_self` — the group relation `T + T = 0` over `F` transports likewise;
* `weilPairingElt_pow_eq_one_of_gS_two_torsion` — `e_2(S, T) ^ n = 1` with the commuting hypothesis
  discharged from the base-field `2`-torsion of `T` (`T + T = 0` in `W.Point`).

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.
-/

open Polynomial

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic] {xT yT : F}

/-- The fixed `F`-point `T = (xT, yT)` on `W` as an element of the group `W.Point`.  Its base change
to `F(W)` is the constant translation point `translatePoint hT`. -/
noncomputable def torsionPoint (hT : W.Equation xT yT) : W.Point :=
  .some xT yT (W.equation_iff_nonsingular.mp hT)

open Classical in
/-- **From the group `2`-torsion relation to the on-curve condition.**  If `T + T = 0` in `W.Point`
for the affine point `T = (xT, yT)`, then `yT = W.negY xT yT` (the affine vertical-tangent
characterisation: `T` equals its own negation `-T = (xT, negY xT yT)`).  In an additive group
`P + P = 0 ↔ P = -P` (`add_eq_zero_iff_eq_neg`); for `T = some xT yT _` the negation is
`some xT (negY xT yT) _` (`Point.neg_some`), so `Point.some.injEq` reads off the `y`-coordinate. -/
theorem negY_of_torsionPoint_add_self (hT : W.Equation xT yT)
    (htors : torsionPoint hT + torsionPoint hT = 0) : yT = W.negY xT yT := by
  rw [add_eq_zero_iff_eq_neg] at htors
  simp only [torsionPoint, Point.neg_some, Point.some.injEq] at htors
  exact htors.2

open Classical in
/-- **On-curve `2`-torsion transports to `F(W)`.**  From the affine `2`-torsion condition
`yT = W.negY xT yT` for `T = (xT, yT)`, the base-changed constant point `translatePoint hT` is
`2`-torsion in `(W ⁄ F(W)).Point`:

```
translatePoint hT + translatePoint hT = 0.
```

Since `translatePoint hT = some (algebraMap F F(W) xT) (algebraMap F F(W) yT) _`, this is
`Point.add_self_of_Y_eq`, whose hypothesis
`algebraMap F F(W) yT = (W ⁄ F(W)).negY (algebraMap F F(W) xT) (algebraMap F F(W) yT)` follows from
the naturality of `negY` under the base-change ring hom (`map_negY`) applied to `yT = W.negY xT yT`.
-/
theorem translatePoint_add_self_of_negY (hT : W.Equation xT yT) (hy : yT = W.negY xT yT) :
    translatePoint hT + translatePoint hT = 0 := by
  apply Point.add_self_of_Y_eq
  rw [map_negY, ← hy]

open Classical in
/-- **The base-field group `2`-torsion of `T` discharges `htors`.**  If `T + T = 0` in `W.Point`,
then `translatePoint hT + translatePoint hT = 0` in `(W ⁄ F(W)).Point` — the exact commuting datum
consumed by the `n = 2` `hcomm` discharge.  Composes `negY_of_torsionPoint_add_self` with
`translatePoint_add_self_of_negY`. -/
theorem translatePoint_add_self (hT : W.Equation xT yT)
    (htors : torsionPoint hT + torsionPoint hT = 0) :
    translatePoint hT + translatePoint hT = 0 :=
  translatePoint_add_self_of_negY hT (negY_of_torsionPoint_add_self hT htors)

open Classical in
/-- **`e_2(S, T) ^ n = 1` from the base-field `2`-torsion of `T`.**  Feeds the transported relation
`translatePoint_add_self` into `weilPairingElt_pow_eq_one_of_gS_torsion`, so the Weil-pairing
element's `n`-th-root-of-unity property is now discharged from the honest group-theoretic
`2`-torsion of `T` over the base field `F` (`T + T = 0` in `W.Point`), with no remaining
function-field hypothesis. -/
theorem weilPairingElt_pow_eq_one_of_gS_two_torsion (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0)
    (htors : torsionPoint hT + torsionPoint hT = 0)
    {f g : W.FunctionField} {u : W.CoordinateRingˣ} {n : ℕ} (hg : g ≠ 0)
    (hu : (u : W.CoordinateRing) • g ^ n = mulByTwoEndo h2 f) :
    weilPairingElt hT g ^ n = 1 :=
  weilPairingElt_pow_eq_one_of_gS_torsion hT h2 (translatePoint_add_self hT htors) hg hu

end CoordinateRing

end WeierstrassCurve.Affine
