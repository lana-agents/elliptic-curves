/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairingProductRelationMu

/-!
# Translation-slot bilinearity of the Weil pairing, unconditionally over `F̄` (rung 6)

For a fixed root `g` the Weil pairing is multiplicative in its **translation** slot:

```
e_n(P, S) · e_n(Q, S) = e_n(P ⊕ Q, S).
```

This is the other half of bilinearity from
`EllipticCurves.FunctionField.WeilPairingDivisorSlotBilinear` (`#861`), and it is the last of the
four slots of `#419` to be instantiated.  Five theorems on `main` state it —
`weilPairingElt_translatePoint_add{,_of_const}` (`WeilPairingBilinear`, `#450`),
`weilPairingElt_translatePoint_add_of_pow_eq_one` (`WeilPairingConstant`),
`weilPairingElt_translatePoint_add_of_baseField` (`WeilPairingBilinearBaseField`, `#451`) and
`weilPairingMu_translatePoint_add_of_baseField` (`WeilPairingBilinearMu`, `#459`) — and every one
of them carries the root `g` and its root-of-unity data as hypotheses.  Outside their home files
the only use was *inside* antisymmetry's proof (`WeilPairingAntisymmetric`), with the data still
carried.  This file instantiates them, at `n = 2` and `n = 3` over an algebraically closed field,
with no hypothesis beyond the setting.

## ⚠️ At the `F(W)` level this needs the torsion of only *one* of the three points

`weilPairingElt_translatePoint_add_of_baseField` takes `hpow : e_n(Q, g) ^ n = 1` at **`Q` alone**;
nothing is assumed about `P` or `R` beyond the group relation `P ⊕ Q = R`.  That asymmetry is not
an artefact of the proof.  The composition law gives `τ_R = τ_P ∘ τ_Q`, so the only quantity that
has to be pushed through `τ_P` is the value `e_n(Q, g)`, and `hpow` is exactly what makes that
value a constant of `F`, hence fixed by every translation.  `P` and `R` are never touched.

So the two headlines below assume different things, deliberately:

* `exists_weilPairingElt_translatePoint_add_{two,three}` takes `hmQ` and `hmS`, and **not** `hmP`;
* `exists_weilPairingMu_translatePoint_add_{two,three}` takes `hmP` as well.

⚠️ The `μ_n(F)` forms need `P`'s torsion for a **type-theoretic** reason, not a mathematical one:
`weilPairingMu h hpow` is *indexed by* `hpow`, so one cannot so much as write down
`weilPairingMu hP …` without first producing `P`'s root-of-unity datum.  Nothing about the
mathematics of the translation slot changes between the two levels.  `R`'s torsion is derived from
`hadd` in both, never assumed, since `W.torsion n` is an `AddSubgroup`.

## ⚠️ Cheaper again than the divisor slot, and the reason is worth recording

`#861` observed that divisor-slot bilinearity consumes no alternating property, and so is cheaper
than antisymmetry (`WeilPairingProductRelation`, `#845`), which consumes it at three points.  The
translation slot is cheaper still: it consumes **no product relation** either, so
`exists_prod_eq_of_pullback` is not in its path at all, and it needs rung-5 data at **one** point
rather than three.

| | rung-5 roots | product relation | alternating property |
|---|---|---|---|
| antisymmetry (`#845`) | 3 | yes | at 3 points |
| divisor slot (`#861`) | 3 | yes | none |
| translation slot (here) | **1** | **none** | **none** |

> The generalisable point, one rung on from `#861`'s: **a slot deferred alongside a harder slot
> inherits the harder slot's gate in the reader's mind.**  `#861` found the divisor slot sitting
> behind antisymmetry's alternating gate without needing it; the translation slot has been sitting
> behind the divisor slot's `hprod` gate without needing that either.

## The route

One rung-5 datum at `S` from `exists_gS_{two,three}_of_isAlgClosed` (`#791`/`#825`) — the only place
`[IsAlgClosed F]` enters, i.e. only through `hprin`; then `hpow` at each translation point from
`weilPairingElt_pow_eq_one_of_gS_two_torsion` (`TranslationTorsion`) /
`weilPairingElt_pow_eq_one_of_gS_three_baseField` (`TranslationTriplingComm`), all with the **same**
`g`; then one application of the translation-slot theorem.

⚠️ Note the shape against `#861`: there, one translation point and three roots; here, three
translation points and **one** root.

⚠️ **There is no descent lemma here**, and this is the one place on this front where the
`#855`/`#859`/`#861` recipe — *lift the conclusion, not the theorem* — does not apply.  Those three
each faced a `μ_n(F)` theorem whose proof ended in a single `exact` at the `F(W)` level, and each
generalised it by binding that conclusion.  `weilPairingMu_translatePoint_add_of_baseField` already
takes its three `hpow` as ordinary hypotheses, so its envelope is already the right one and it is
applied directly.  A reader looking for the `exact` to bind will not find one.

## Main results

* `exists_weilPairingElt_translatePoint_add_two` and `_three` — translation-slot bilinearity at the
  `F(W)` level over `F̄` with no hypothesis beyond the setting;
* `exists_weilPairingMu_translatePoint_add_two` and `_three` — the same in `μ_n(F)`, with the three
  `hpow` data produced rather than assumed.

## Scope

`[Field F] [IsAlgClosed F] {W : Affine F} [W.IsElliptic]` throughout.

Out of scope: `hprin` over a **general** field, open at both `n`, which is what confines these to
`F̄`; general `n` (`#404`'s `ωₙ`); rung 4 (`#414`/`#421`/`#422`), which is not in this path;
non-degeneracy; bundling into `weilPairingMuHom` — `WeilPairingDivisorSlotHom` explains why the
translation slot wants a map out of the torsion subgroup of `W.Point` rather than out of a
subobject of `F(W)`, and nothing here touches that obstruction; any change to the five existing
`translatePoint_add` theorems or their proofs.

⚠️ **The two slots are combined elsewhere, and not by extending either of them.**  This bullet
used to read *"The two slots are not combined into a single bilinearity statement.  That would want
a pairing defined on `W.Point × W.Point`; there is none in this tree …"*.  The **route it predicted
is what was wrong**: the combination did not arrive by extending the pairing up to `W.Point`, it
arrived by restricting it down to `E[n]`.
`EllipticCurves.FunctionField.WeilPairingFunctionTwo` (`#922`) makes `e_2` a function of two torsion
points and bundles it as
`weilPairingTwoHom : Multiplicative E[2] →* (Multiplicative E[2] →* μ_2(F))`, whose two `map_mul'`
fields are `weilPairingTwo_add_left` and `weilPairingTwo_add_right` — bilinearity in both slots, in
one object.  `WeilPairingFunctionThree` (`#925`) is the `n = 3` mirror.

⚠️ **The literal claim about `W.Point × W.Point` is still true and is not the same claim.**  There
is no pairing on `W.Point × W.Point` in this tree, and `#922`'s scope section argues there cannot
usefully be one: the rung-5 root exists only at torsion points.  Combining the two slots *at this
level* — where the divisor slot is a slot of `weilPairingElt`, which takes a *function* — remains a
separate piece of work with a separate design question, and is not a corollary of these four
theorems.

## Non-vacuity

Every headline is certified below on the two curves of `#845`/`#861`.

⚠️ **At `n = 2` the certificate is a genuine three-point instance and every point of the statement
is named.**  On `y² = x³ − x` the three nonzero `2`-torsion points are `(0, 0)`, `(1, 0)` and
`(−1, 0)`, and they are exactly `P`, `Q` and `R` with `P ⊕ Q = R`; the divisor point `S` is a free
variable of the statement and is taken to be `(0, 0)`.  The only coincidence is `S = P`, which the
statement does not constrain — contrast `#861`, which needed three *divisor* points and so had no
fourth point left for the translation slot.

At `n = 3` the usual limitation bites: on `y² + y = x³` only `(0, 0)` and its negative `(0, −1)`
are nameable — `Ψ₃ = 3X(X³ + 1)`, and the `X = −1` fibre is `y² + y + 1 = 0`, whose roots are
primitive cube roots of unity — so `P = Q = S = (0, 0)` and `R = (0, −1)` is forced.  The
certificate shows the hypotheses are simultaneously satisfiable, which is what it is for; it does
not exhibit `P ≠ Q`.  Stated, not repaired.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(a).
-/

namespace WeierstrassCurve.Affine

open CoordinateRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

section Two

variable [IsAlgClosed F]

open Classical in
/-- **Translation-slot bilinearity at `n = 2`, over `F̄` with no hypothesis beyond the setting.**

```
e_2(R, g) = e_2(P, g) · e_2(Q, g),     for  P ⊕ Q = R.
```

The single root is produced together with its rung-5 certificate, as in `#845`/`#861`; unlike those
it is produced at the **divisor** point `S`, which the three translation points `P`, `Q`, `R` do
not constrain.

⚠️ Only `Q`'s `2`-torsion is assumed, alongside `S`'s:
`weilPairingElt_translatePoint_add_of_baseField` needs the pairing value to be a constant at the
*middle* point only.  See the module docstring.
`[IsAlgClosed F]` enters through `exists_gS_two_of_isAlgClosed` (`#791`) alone. -/
theorem exists_weilPairingElt_translatePoint_add_two (h2 : (2 : F) ≠ 0)
    {xP yP xQ yQ xR yR xS yS : F} (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
    (hR : W.Nonsingular xR yR) (hS : W.Nonsingular xS yS)
    (hmQ : Point.some xQ yQ hQ ∈ W.torsion 2) (hmS : Point.some xS yS hS ∈ W.torsion 2)
    (hadd : Point.some xP yP hP + Point.some xQ yQ hQ = Point.some xR yR hR) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
      weilPairingElt hR.left g = weilPairingElt hP.left g * weilPairingElt hQ.left g := by
  obtain ⟨f, hf, hd, g, hg, u, hu⟩ := exists_gS_two_of_isAlgClosed h2 hS hmS
  have hpowQ : weilPairingElt hQ.left g ^ 2 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_two_torsion hQ.left h2
      (add_self_eq_zero_of_mem_torsion_two hmQ) hg hu
  exact ⟨g, hg, ⟨f, hf, hd, u, hu⟩,
    weilPairingElt_translatePoint_add_of_baseField hP.left hQ.left hR.left hadd hg two_ne_zero
      hpowQ⟩

open Classical in
/-- **Translation-slot bilinearity at `n = 2` in `μ_n(F)`, over `F̄` with no hypothesis beyond the
setting.**

```
μ_n(R, g) = μ_n(P, g) · μ_n(Q, g)   in rootsOfUnity n F.
```

The envelope is `exists_weilPairingElt_translatePoint_add_two`'s, extended by the three `hpow`
data: they are bound existentially because `weilPairingMu` is indexed by the *proof*, and they are
**produced** — not assumed — from the single rung-5 certificate the envelope already carries, by
`weilPairingElt_pow_eq_one_of_gS_two_torsion` (`TranslationTorsion`) applied at each of `P`, `Q`,
`R` with that one root.

⚠️ `hmP` is required here and is not in the `F(W)`-level headline.  That is a consequence of
`weilPairingMu` being indexed by `hpow` — see the module docstring — and not of the mathematics
changing.  `hmR` is derived from `hadd`, not assumed. -/
theorem exists_weilPairingMu_translatePoint_add_two (h2 : (2 : F) ≠ 0)
    {xP yP xQ yQ xR yR xS yS : F} (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
    (hR : W.Nonsingular xR yR) (hS : W.Nonsingular xS yS)
    (hmP : Point.some xP yP hP ∈ W.torsion 2) (hmQ : Point.some xQ yQ hQ ∈ W.torsion 2)
    (hmS : Point.some xS yS hS ∈ W.torsion 2)
    (hadd : Point.some xP yP hP + Point.some xQ yQ hQ = Point.some xR yR hR) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
      ∃ hpowP : weilPairingElt hP.left g ^ 2 = 1,
        ∃ hpowQ : weilPairingElt hQ.left g ^ 2 = 1,
          ∃ hpowR : weilPairingElt hR.left g ^ 2 = 1,
            weilPairingMu hR.left hpowR
              = weilPairingMu hP.left hpowP * weilPairingMu hQ.left hpowQ := by
  have hmR : Point.some xR yR hR ∈ W.torsion 2 := hadd ▸ add_mem hmP hmQ
  obtain ⟨f, hf, hd, g, hg, u, hu⟩ := exists_gS_two_of_isAlgClosed h2 hS hmS
  have hpowP : weilPairingElt hP.left g ^ 2 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_two_torsion hP.left h2
      (add_self_eq_zero_of_mem_torsion_two hmP) hg hu
  have hpowQ : weilPairingElt hQ.left g ^ 2 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_two_torsion hQ.left h2
      (add_self_eq_zero_of_mem_torsion_two hmQ) hg hu
  have hpowR : weilPairingElt hR.left g ^ 2 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_two_torsion hR.left h2
      (add_self_eq_zero_of_mem_torsion_two hmR) hg hu
  exact ⟨g, hg, ⟨f, hf, hd, u, hu⟩, hpowP, hpowQ, hpowR,
    weilPairingMu_translatePoint_add_of_baseField hP.left hQ.left hR.left hadd hg hpowP hpowQ
      hpowR⟩

end Two

section Three

variable [IsAlgClosed F]

open Classical in
/-- **Translation-slot bilinearity at `n = 3`, over `F̄` with no hypothesis beyond the setting.**

The `n = 3` mirror of `exists_weilPairingElt_translatePoint_add_two`; only the pullback differs,
`mulByThreeEndo h2 h3` in place of `mulByTwoEndo h2`, and with it the rung-5 producer
(`exists_gS_three_of_isAlgClosed`, `#825`) and the `hpow` producer
(`weilPairingElt_pow_eq_one_of_gS_three_baseField`, `TranslationTriplingComm`).  As at `n = 2`,
only `Q`'s torsion is assumed among the three translation points. -/
theorem exists_weilPairingElt_translatePoint_add_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xP yP xQ yQ xR yR xS yS : F} (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
    (hR : W.Nonsingular xR yR) (hS : W.Nonsingular xS yS)
    (hmQ : Point.some xQ yQ hQ ∈ W.torsion 3) (hmS : Point.some xS yS hS ∈ W.torsion 3)
    (hadd : Point.some xP yP hP + Point.some xQ yQ hQ = Point.some xR yR hR) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) ∧
      weilPairingElt hR.left g = weilPairingElt hP.left g * weilPairingElt hQ.left g := by
  obtain ⟨f, hf, hd, g, hg, u, hu⟩ := exists_gS_three_of_isAlgClosed h2 h3 hS hmS
  have hpowQ : weilPairingElt hQ.left g ^ 3 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_three_baseField hQ.left h2 h3
      (add_add_self_eq_zero_of_mem_torsion_three hmQ) hg hu
  exact ⟨g, hg, ⟨f, hf, hd, u, hu⟩,
    weilPairingElt_translatePoint_add_of_baseField hP.left hQ.left hR.left hadd hg three_ne_zero
      hpowQ⟩

open Classical in
/-- **Translation-slot bilinearity at `n = 3` in `μ_n(F)`, over `F̄` with no hypothesis beyond the
setting.**  The `n = 3` mirror of `exists_weilPairingMu_translatePoint_add_two`; the three `hpow`
data come from `weilPairingElt_pow_eq_one_of_gS_three_baseField` (`TranslationTriplingComm`) in
place of `weilPairingElt_pow_eq_one_of_gS_two_torsion`. -/
theorem exists_weilPairingMu_translatePoint_add_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xP yP xQ yQ xR yR xS yS : F} (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
    (hR : W.Nonsingular xR yR) (hS : W.Nonsingular xS yS)
    (hmP : Point.some xP yP hP ∈ W.torsion 3) (hmQ : Point.some xQ yQ hQ ∈ W.torsion 3)
    (hmS : Point.some xS yS hS ∈ W.torsion 3)
    (hadd : Point.some xP yP hP + Point.some xQ yQ hQ = Point.some xR yR hR) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) ∧
      ∃ hpowP : weilPairingElt hP.left g ^ 3 = 1,
        ∃ hpowQ : weilPairingElt hQ.left g ^ 3 = 1,
          ∃ hpowR : weilPairingElt hR.left g ^ 3 = 1,
            weilPairingMu hR.left hpowR
              = weilPairingMu hP.left hpowP * weilPairingMu hQ.left hpowQ := by
  have hmR : Point.some xR yR hR ∈ W.torsion 3 := hadd ▸ add_mem hmP hmQ
  obtain ⟨f, hf, hd, g, hg, u, hu⟩ := exists_gS_three_of_isAlgClosed h2 h3 hS hmS
  have hpowP : weilPairingElt hP.left g ^ 3 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_three_baseField hP.left h2 h3
      (add_add_self_eq_zero_of_mem_torsion_three hmP) hg hu
  have hpowQ : weilPairingElt hQ.left g ^ 3 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_three_baseField hQ.left h2 h3
      (add_add_self_eq_zero_of_mem_torsion_three hmQ) hg hu
  have hpowR : weilPairingElt hR.left g ^ 3 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_three_baseField hR.left h2 h3
      (add_add_self_eq_zero_of_mem_torsion_three hmR) hg hu
  exact ⟨g, hg, ⟨f, hf, hd, u, hu⟩, hpowP, hpowQ, hpowR,
    weilPairingMu_translatePoint_add_of_baseField hP.left hQ.left hR.left hadd hg hpowP hpowQ
      hpowR⟩

end Three

/-! ### Non-vacuity

⚠️ See the module docstring for what the two certificates exhibit.  At `n = 2` every point of the
statement is named and `P`, `Q`, `R` are distinct; at `n = 3` the curve forces `P = Q = S`. -/

section Nonvacuity

/-- An algebraically closed field of characteristic zero. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

private lemma exampleTwo : (2 : exampleField) ≠ 0 := by norm_num

private lemma exampleThree : (3 : exampleField) ≠ 0 := by norm_num

/-- The curve `y² = x³ − x` over `AlgebraicClosure ℚ`, of discriminant `64`. -/
private noncomputable def exampleCurve : Affine exampleField := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleNsP : exampleCurve.Nonsingular 0 0 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

private lemma exampleNsQ : exampleCurve.Nonsingular 1 0 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

private lemma exampleNsR : exampleCurve.Nonsingular (-1) 0 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

open Classical in
private lemma exampleTorP :
    Point.some (0 : exampleField) 0 exampleNsP ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNsP).mpr (by norm_num [exampleCurve])

open Classical in
private lemma exampleTorQ :
    Point.some (1 : exampleField) 0 exampleNsQ ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNsQ).mpr (by norm_num [exampleCurve])

open Classical in
/-- `(0, 0) ⊕ (1, 0) = (−1, 0)` on `y² = x³ − x`: the three nonzero `2`-torsion points, and they
are **distinct**. -/
private lemma exampleAdd :
    Point.some (0 : exampleField) 0 exampleNsP + Point.some (1 : exampleField) 0 exampleNsQ
      = Point.some (-1 : exampleField) 0 exampleNsR := by
  rw [Point.add_of_X_ne (by norm_num)]
  simp only [Point.some.injEq]
  norm_num [exampleCurve, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.negY]

open Classical in
/-- **Translation-slot bilinearity at `n = 2` on a curve that exists.**  `P = (0, 0)`,
`Q = (1, 0)`, `R = (−1, 0)` are the three distinct nonzero `2`-torsion points of `y² = x³ − x`, so
`P ⊕ Q = R` is a genuine three-point instance; the divisor point is `S = P`, which the statement
leaves free. -/
example : ∃ g : exampleCurve.FunctionField,
    weilPairingElt exampleNsR.left g
      = weilPairingElt exampleNsP.left g * weilPairingElt exampleNsQ.left g := by
  obtain ⟨g, _, _, hbil⟩ :=
    exists_weilPairingElt_translatePoint_add_two exampleTwo exampleNsP exampleNsQ exampleNsR
      exampleNsP exampleTorQ exampleTorP exampleAdd
  exact ⟨g, hbil⟩

open Classical in
/-- **Translation-slot bilinearity at `n = 2` in `μ_2(F)`, on a curve that exists.**  As above; the
three `hpow` data are produced inside the headline from its single rung-5 certificate, so they are
not an extra burden on the caller — they are bound here because `weilPairingMu` is indexed by
them. -/
example : ∃ (g : exampleCurve.FunctionField)
    (hpowP : weilPairingElt exampleNsP.left g ^ 2 = 1)
    (hpowQ : weilPairingElt exampleNsQ.left g ^ 2 = 1)
    (hpowR : weilPairingElt exampleNsR.left g ^ 2 = 1),
    weilPairingMu exampleNsR.left hpowR
      = weilPairingMu exampleNsP.left hpowP * weilPairingMu exampleNsQ.left hpowQ := by
  obtain ⟨g, _, _, hpowP, hpowQ, hpowR, hbil⟩ :=
    exists_weilPairingMu_translatePoint_add_two exampleTwo exampleNsP exampleNsQ exampleNsR
      exampleNsP exampleTorP exampleTorQ exampleTorP exampleAdd
  exact ⟨g, hpowP, hpowQ, hpowR, hbil⟩

/-- The curve `y² + y = x³` over `AlgebraicClosure ℚ`, of discriminant `−27`. -/
private noncomputable def exampleCurveThree : Affine exampleField := ⟨0, 0, 1, 0, 0⟩

private instance : exampleCurveThree.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurveThree, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleNsThreeP : exampleCurveThree.Nonsingular 0 0 :=
  exampleCurveThree.equation_iff_nonsingular.mp (by
    norm_num [exampleCurveThree, WeierstrassCurve.Affine.equation_iff])

private lemma exampleNsThreeR : exampleCurveThree.Nonsingular 0 (-1) :=
  exampleCurveThree.equation_iff_nonsingular.mp (by
    norm_num [exampleCurveThree, WeierstrassCurve.Affine.equation_iff])

open Classical in
private lemma exampleTorThreeP :
    Point.some (0 : exampleField) 0 exampleNsThreeP ∈ exampleCurveThree.torsion 3 :=
  mem_torsion_three_some_iff'.mpr (by
    norm_num [exampleCurveThree, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈])

open Classical in
/-- `(0, 0) ⊕ (0, 0) = (0, −1)` on `y² + y = x³`: doubling the named `3`-torsion point gives its
negative, which is the other one. -/
private lemma exampleAddThree :
    Point.some (0 : exampleField) 0 exampleNsThreeP
        + Point.some (0 : exampleField) 0 exampleNsThreeP
      = Point.some (0 : exampleField) (-1) exampleNsThreeR := by
  rw [Point.add_of_Y_ne (by norm_num [exampleCurveThree, WeierstrassCurve.Affine.negY])]
  simp only [Point.some.injEq]
  norm_num [exampleCurveThree, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.negY]

open Classical in
/-- **Translation-slot bilinearity at `n = 3` on a curve that exists.**  ⚠️ Here `P = Q = S =
(0, 0)` and `R = (0, −1)`; see the module docstring for why no other `3`-torsion point of
`y² + y = x³` is nameable. -/
example : ∃ g : exampleCurveThree.FunctionField,
    weilPairingElt exampleNsThreeR.left g
      = weilPairingElt exampleNsThreeP.left g * weilPairingElt exampleNsThreeP.left g := by
  obtain ⟨g, _, _, hbil⟩ :=
    exists_weilPairingElt_translatePoint_add_three exampleTwo exampleThree exampleNsThreeP
      exampleNsThreeP exampleNsThreeR exampleNsThreeP exampleTorThreeP exampleTorThreeP
      exampleAddThree
  exact ⟨g, hbil⟩

open Classical in
/-- **Translation-slot bilinearity at `n = 3` in `μ_3(F)`, on a curve that exists.**  ⚠️ Here
`P = Q = S = (0, 0)`; see the module docstring. -/
example : ∃ (g : exampleCurveThree.FunctionField)
    (hpowP : weilPairingElt exampleNsThreeP.left g ^ 3 = 1)
    (hpowR : weilPairingElt exampleNsThreeR.left g ^ 3 = 1),
    weilPairingMu exampleNsThreeR.left hpowR
      = weilPairingMu exampleNsThreeP.left hpowP * weilPairingMu exampleNsThreeP.left hpowP := by
  obtain ⟨g, _, _, hpowP, _, hpowR, hbil⟩ :=
    exists_weilPairingMu_translatePoint_add_three exampleTwo exampleThree exampleNsThreeP
      exampleNsThreeP exampleNsThreeR exampleNsThreeP exampleTorThreeP exampleTorThreeP
      exampleTorThreeP exampleAddThree
  exact ⟨g, hpowP, hpowR, hbil⟩

end Nonvacuity

end WeierstrassCurve.Affine
