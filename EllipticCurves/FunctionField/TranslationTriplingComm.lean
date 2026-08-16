/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.GenericTripling
import EllipticCurves.FunctionField.TranslationComposition
import EllipticCurves.FunctionField.TranslationTorsionMap
import EllipticCurves.FunctionField.WeilPairing

/-!
# Discharging `hcomm` for the `n = 3` Weil-pairing element from a torsion hypothesis

Let `W` be an elliptic curve over a field `F` of characteristic `≠ 2, 3`, with a fixed affine point
`T = (xT, yT)` on `W` (`hT : W.Equation xT yT`).  The rung-6 Weil-pairing element
(`FunctionField/WeilPairing.lean`, #419) still carries the commuting hypothesis

```
hcomm : translateEndo hT ([3]∗ f) = [3]∗ f       -- [3]∗ = mulByThreeEndo, i.e. [3](P + T) = [3]P
```

This file discharges `hcomm` for `n = 3` from the clean group-theoretic hypothesis that `T` is a
`3`-torsion point (in the base-changed group `(W ⁄ F(W)).Point`):

```
htors : translatePoint hT + translatePoint hT + translatePoint hT = 0.
```

It is the exact `mulByThreeEndo` mirror of the merged `n = 2`
`FunctionField/TranslationDoublingComm.lean` (#164); the one wrinkle is that tripling is the
two-step secant sum `(2•𝒫) + 𝒫`, so the naturality push goes through the doubled point first.

## Main results

* `translateEndo_mulByThreeEndo_gen` — the two generator identities
  `translateEndo hT (mulByThreeEndo h2 h3 (genX W)) = mulByThreeEndo h2 h3 (genX W)` and the `genY`
  analogue;
* `translateEndo_mulByThreeEndo_comp` — the operator identity
  `translateEndo hT ∘ mulByThreeEndo h2 h3 = mulByThreeEndo h2 h3`;
* `translateEndo_mulByThreeEndo_apply` — its applied form
  `translateEndo hT (mulByThreeEndo h2 h3 f) = mulByThreeEndo h2 h3 f` for every `f : F(W)`;
* `weilPairingElt_pow_eq_one_of_gS_three_torsion` — `e_3(S, T) ^ n = 1`, with `hcomm` discharged and
  only the `F(W)`-level torsion hypothesis `htors` remaining;
* `weilPairingElt_pow_eq_one_of_gS_three_baseField` — the same, but discharged from the honest
  base-field `3`-torsion of `T` (`T + T + T = 0` in `W.Point`), with no `F(W)`-level hypothesis; the
  `n = 3` mirror of `weilPairingElt_pow_eq_one_of_gS_two_torsion`
  (`FunctionField/TranslationTorsion.lean`).

## The route (no new ring computation)

Reading `translateEndo hT` as `+ 𝒯` (`genericPoint_add_translatePoint`) and `mulByThreeEndo h2 h3`
as the group triple `𝒫 ↦ 𝒫 + 𝒫 + 𝒫 = [3]•𝒫` (`genericPoint_add_add_self`, #443), and writing
`𝒬 := 𝒫 + 𝒯`, the commuting identity on the generic point is the group calculation

```
𝒬 + 𝒬 + 𝒬 = (𝒫 + 𝒫 + 𝒫) + (𝒯 + 𝒯 + 𝒯) = 𝒫 + 𝒫 + 𝒫      (using 𝒯 + 𝒯 + 𝒯 = 0).
```

The left-hand side is computed via the affine addition law from `𝒬`'s coordinates
`(translateEndo hT (genX W), translateEndo hT (genY W))`:

* `𝒬` is not `2`-torsion (`translateEndo` is injective and fixes the base, transporting
  `genY_ne_negY_gen`), so `𝒬 + 𝒬` takes the tangent branch; pushing `translateEndo` through the
  doubling coordinates (`addX_gen_eq_mulByTwo`/`_mulByTwo`) gives
  `𝒬 + 𝒬 = (translateEndo hT (mulByTwoEndo h2 (genX W)), …)`;
* `x(2•𝒬) ≠ x(𝒬)` (injectivity applied to `mulByTwoEndo_genX_ne_genX`), so `(2•𝒬) + 𝒬` is a secant
  sum; pushing `translateEndo` through the tripling coordinates
  (`addX_gen_eq_mulByThree`/`_mulByThree`) gives
  `𝒬 + 𝒬 + 𝒬 = (translateEndo hT (mulByThreeEndo …), …)`.

Comparing coordinates against `𝒫 + 𝒫 + 𝒫 = (mulByThreeEndo …, …)` yields the generator identities,
and the fraction-field/`AdjoinRoot` ext (mirroring `translateEndo_comp`) upgrades those to the full
operator identity.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.
-/

open Polynomial

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic] {xT yT : F}

open Classical in
/-- **The generator identities for `translateEndo hT ∘ mulByThreeEndo h2 h3` from `3`-torsion.**
For a `3`-torsion point `T`
(`htors : translatePoint hT + translatePoint hT + translatePoint hT = 0`), the translation `+ 𝒯`
fixes the tripling images of the coordinate generators:

```
translateEndo hT (mulByThreeEndo h2 h3 (genX W)) = mulByThreeEndo h2 h3 (genX W)   (and genY).
```

The proof reads both sides in the group `(W ⁄ F(W)).Point`, computing `𝒬 + 𝒬 + 𝒬` (with
`𝒬 = 𝒫 + 𝒯`) as a two-step secant sum in `𝒬`'s coordinates, then using
`𝒬 + 𝒬 + 𝒬 = 𝒫 + 𝒫 + 𝒫` (from `𝒯 + 𝒯 + 𝒯 = 0`) to identify it with `(mulByThreeEndo …, …)`. -/
theorem translateEndo_mulByThreeEndo_gen (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0)
    (htors : translatePoint hT + translatePoint hT + translatePoint hT = 0) :
    translateEndo hT (mulByThreeEndo h2 h3 (genX W)) = mulByThreeEndo h2 h3 (genX W)
      ∧ translateEndo hT (mulByThreeEndo h2 h3 (genY W)) = mulByThreeEndo h2 h3 (genY W) := by
  -- `translateEndo hT` maps the base-changed curve to itself (it fixes the base map `F → F(W)`).
  have hcurve : (W.map (algebraMap F W.FunctionField)).map (translateEndo hT)
      = W.map (algebraMap F W.FunctionField) := by
    have hcomp : (translateEndo hT).comp (algebraMap F W.FunctionField)
        = algebraMap F W.FunctionField := RingHom.ext (translateEndo_algebraMap_base hT)
    simp only [WeierstrassCurve.map_map, hcomp]
  -- Naturality of `negY` at the generic point.
  have hnegY : translateEndo hT ((W.map (algebraMap F W.FunctionField)).negY (genX W) (genY W))
      = (W.map (algebraMap F W.FunctionField)).negY
          (translateEndo hT (genX W)) (translateEndo hT (genY W)) := by
    have h := WeierstrassCurve.Affine.map_negY (W' := W.map (algebraMap F W.FunctionField))
      (f := translateEndo hT) (x := genX W) (y := genY W)
    rw [hcurve] at h; exact h.symm
  -- STEP 1: `𝒬 = 𝒫 + 𝒯` is not `2`-torsion.
  have hYne : translateEndo hT (genY W)
      ≠ (W.map (algebraMap F W.FunctionField)).negY
          (translateEndo hT (genX W)) (translateEndo hT (genY W)) := by
    rw [← hnegY]
    exact fun hy => genY_ne_negY_gen h2 ((translateEndo hT).injective hy)
  -- STEP 2: naturality of the doubling coordinates (torsion-free).
  have hdoubleX : (W.map (algebraMap F W.FunctionField)).addX
        (translateEndo hT (genX W)) (translateEndo hT (genX W))
        ((W.map (algebraMap F W.FunctionField)).slope
          (translateEndo hT (genX W)) (translateEndo hT (genX W))
          (translateEndo hT (genY W)) (translateEndo hT (genY W)))
      = translateEndo hT (mulByTwoEndo h2 (genX W)) := by
    rw [← addX_gen_eq_mulByTwo h2, translateEndo_addX, translateEndo_slope]
  have hdoubleY : (W.map (algebraMap F W.FunctionField)).addY
        (translateEndo hT (genX W)) (translateEndo hT (genX W)) (translateEndo hT (genY W))
        ((W.map (algebraMap F W.FunctionField)).slope
          (translateEndo hT (genX W)) (translateEndo hT (genX W))
          (translateEndo hT (genY W)) (translateEndo hT (genY W)))
      = translateEndo hT (mulByTwoEndo h2 (genY W)) := by
    rw [← addY_gen_eq_mulByTwo h2, translateEndo_addY, translateEndo_slope]
  -- Nonsingularity of the doubled coordinates.
  have hns2 : (W.map (algebraMap F W.FunctionField)).Nonsingular
      (translateEndo hT (mulByTwoEndo h2 (genX W)))
      (translateEndo hT (mulByTwoEndo h2 (genY W))) := by
    rw [← hdoubleX, ← hdoubleY]
    exact nonsingular_add (nonsingular_translateEndo_gen hT) (nonsingular_translateEndo_gen hT)
      (fun hxy => hYne hxy.right)
  -- `𝒬` and `𝒬 + 𝒬` as `Point.some`.
  have hQeq : genericPoint + translatePoint hT
      = Point.some (translateEndo hT (genX W)) (translateEndo hT (genY W))
          (nonsingular_translateEndo_gen hT) := genericPoint_add_translatePoint hT
  have hQQ : (genericPoint + translatePoint hT) + (genericPoint + translatePoint hT)
      = Point.some (translateEndo hT (mulByTwoEndo h2 (genX W)))
          (translateEndo hT (mulByTwoEndo h2 (genY W))) hns2 := by
    rw [hQeq, Point.add_self_of_Y_ne hYne, Point.some.injEq]
    exact ⟨hdoubleX, hdoubleY⟩
  -- STEP 3: naturality of the tripling coordinates (the secant `(2•𝒬) + 𝒬`).
  have hAX : (W.map (algebraMap F W.FunctionField)).addX
        (translateEndo hT (mulByTwoEndo h2 (genX W))) (translateEndo hT (genX W))
        ((W.map (algebraMap F W.FunctionField)).slope
          (translateEndo hT (mulByTwoEndo h2 (genX W))) (translateEndo hT (genX W))
          (translateEndo hT (mulByTwoEndo h2 (genY W))) (translateEndo hT (genY W)))
      = translateEndo hT (mulByThreeEndo h2 h3 (genX W)) := by
    rw [← addX_gen_eq_mulByThree h2 h3, translateEndo_addX, translateEndo_slope]
  have hAY : (W.map (algebraMap F W.FunctionField)).addY
        (translateEndo hT (mulByTwoEndo h2 (genX W))) (translateEndo hT (genX W))
        (translateEndo hT (mulByTwoEndo h2 (genY W)))
        ((W.map (algebraMap F W.FunctionField)).slope
          (translateEndo hT (mulByTwoEndo h2 (genX W))) (translateEndo hT (genX W))
          (translateEndo hT (mulByTwoEndo h2 (genY W))) (translateEndo hT (genY W)))
      = translateEndo hT (mulByThreeEndo h2 h3 (genY W)) := by
    rw [← addY_gen_eq_mulByThree h2 h3, translateEndo_addY, translateEndo_slope]
  have hXne : translateEndo hT (mulByTwoEndo h2 (genX W)) ≠ translateEndo hT (genX W) :=
    fun h => mulByTwoEndo_genX_ne_genX h2 h3 ((translateEndo hT).injective h)
  have hns3 : (W.map (algebraMap F W.FunctionField)).Nonsingular
      (translateEndo hT (mulByThreeEndo h2 h3 (genX W)))
      (translateEndo hT (mulByThreeEndo h2 h3 (genY W))) := by
    rw [← hAX, ← hAY]
    exact nonsingular_add hns2 (nonsingular_translateEndo_gen hT) (fun hxy => hXne hxy.left)
  -- The LHS `𝒬 + 𝒬 + 𝒬` in coordinates.
  have hLHS : (genericPoint + translatePoint hT) + (genericPoint + translatePoint hT)
        + (genericPoint + translatePoint hT)
      = Point.some (translateEndo hT (mulByThreeEndo h2 h3 (genX W)))
          (translateEndo hT (mulByThreeEndo h2 h3 (genY W))) hns3 := by
    rw [hQQ, hQeq, Point.add_of_X_ne hXne, Point.some.injEq]
    exact ⟨hAX, hAY⟩
  -- STEP 4: the group calculation `𝒬 + 𝒬 + 𝒬 = 𝒫 + 𝒫 + 𝒫`.
  have hRHS : (genericPoint + translatePoint hT) + (genericPoint + translatePoint hT)
        + (genericPoint + translatePoint hT)
      = genericPoint + genericPoint + genericPoint := by
    have hreassoc : (genericPoint + translatePoint hT) + (genericPoint + translatePoint hT)
          + (genericPoint + translatePoint hT)
        = (genericPoint + genericPoint + genericPoint)
          + (translatePoint hT + translatePoint hT + translatePoint hT) := by abel
    rw [hreassoc, htors, add_zero]
  have hcombined := hLHS.symm.trans (hRHS.trans (genericPoint_add_add_self h2 h3))
  rw [Point.some.injEq] at hcombined
  exact hcombined

/-- **The operator identity `translateEndo hT ∘ mulByThreeEndo h2 h3 = mulByThreeEndo h2 h3`**, from
`3`-torsion.  Mirrors `translateEndo_comp`: the two homomorphisms agree on `F(W)` iff they agree on
the coordinate ring `F[W]` (`IsFractionRing.ringHom_ext`), which by `AdjoinRoot.ringHom_ext` reduces
to the constants (both fix `algebraMap F F(W) c`) and the two generators `mk W (C X)` and
`AdjoinRoot.root W.polynomial` — exactly the generator identities of
`translateEndo_mulByThreeEndo_gen`. -/
theorem translateEndo_mulByThreeEndo_comp (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0)
    (htors : translatePoint hT + translatePoint hT + translatePoint hT = 0) :
    (translateEndo hT).comp (mulByThreeEndo h2 h3) = mulByThreeEndo h2 h3 := by
  obtain ⟨hx, hy⟩ := translateEndo_mulByThreeEndo_gen hT h2 h3 htors
  -- Reduce to agreement on the coordinate ring, then to the two generators.
  have hcr : (translateEndo hT).comp (mulByThreeCoordHom h2 h3) = mulByThreeCoordHom h2 h3 := by
    refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun c => ?_) ?_) ?_
    · -- constants: both sides reduce to `algebraMap F F(W) c`
      have hofC : AdjoinRoot.of W.polynomial (C c) = algebraMap F W.CoordinateRing c := by
        rw [IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing, AdjoinRoot.algebraMap_eq,
          ← Polynomial.C_eq_algebraMap]
      simp only [RingHom.comp_apply, hofC, mulByThreeCoordHom_algebraMap,
        translateEndo_algebraMap_base]
    · -- the `X`-generator: this is `hx`, read through `genX = algebraMap _ _ (mk (C X))`
      have hxc : translateEndo hT (mulByThreeCoordHom h2 h3 (mk W (C X)))
          = mulByThreeCoordHom h2 h3 (mk W (C X)) := by
        rw [genX, genPsi, mulByThreeEndo_algebraMap] at hx
        exact hx
      simpa only [RingHom.comp_apply,
        show AdjoinRoot.of W.polynomial X = mk W (C X) from rfl] using hxc
    · -- the root generator: this is `hy`, read through `genY = algebraMap _ _ root`
      have hyc : translateEndo hT (mulByThreeCoordHom h2 h3 (AdjoinRoot.root W.polynomial))
          = mulByThreeCoordHom h2 h3 (AdjoinRoot.root W.polynomial) := by
        rw [genY, genPsi, mulByThreeEndo_algebraMap] at hy
        exact hy
      simpa only [RingHom.comp_apply] using hyc
  refine IsFractionRing.ringHom_ext (A := W.CoordinateRing) (fun a => ?_)
  rw [RingHom.comp_apply, mulByThreeEndo_algebraMap]
  exact congr($hcr a)

/-- **The operator identity in applied form.** For every `f : F(W)`,
`translateEndo hT (mulByThreeEndo h2 h3 f) = mulByThreeEndo h2 h3 f`; this is the `hcomm` input
consumed by the rung-6 Weil-pairing element, discharged from the `3`-torsion hypothesis `htors`. -/
theorem translateEndo_mulByThreeEndo_apply (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0)
    (htors : translatePoint hT + translatePoint hT + translatePoint hT = 0) (f : W.FunctionField) :
    translateEndo hT (mulByThreeEndo h2 h3 f) = mulByThreeEndo h2 h3 f := by
  have h := translateEndo_mulByThreeEndo_comp hT h2 h3 htors
  exact congr($h f)

/-- **`e_3(S, T) ^ n = 1` with `hcomm` discharged from `3`-torsion.**  Combines
`weilPairingElt_pow_eq_one_of_gS_three'` (which reduces the `n`-th-root-of-unity property to the
commuting identity `hcomm`) with `translateEndo_mulByThreeEndo_apply` (which discharges `hcomm` for
the tripling map `[3]∗ = mulByThreeEndo` from the `3`-torsion hypothesis `htors`). -/
theorem weilPairingElt_pow_eq_one_of_gS_three_torsion (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0)
    (htors : translatePoint hT + translatePoint hT + translatePoint hT = 0)
    {f g : W.FunctionField} {u : W.CoordinateRingˣ} {n : ℕ} (hg : g ≠ 0)
    (hu : (u : W.CoordinateRing) • g ^ n = mulByThreeEndo h2 h3 f) :
    weilPairingElt hT g ^ n = 1 :=
  weilPairingElt_pow_eq_one_of_gS_three' hT h2 h3 hg hu
    (translateEndo_mulByThreeEndo_apply hT h2 h3 htors f)

open Classical in
/-- **`e_3(S, T) ^ n = 1` from the honest base-field `3`-torsion of `T`.**  Feeds the transported
relation `translatePoint_add_add_self` (#444) into `weilPairingElt_pow_eq_one_of_gS_three_torsion`,
so the Weil-pairing element's `n`-th-root-of-unity property is discharged from the group-theoretic
`3`-torsion of `T` over the base field `F` (`T + T + T = 0` in `W.Point`), with no remaining
function-field hypothesis.  The `n = 3` mirror of `weilPairingElt_pow_eq_one_of_gS_two_torsion`
(`FunctionField/TranslationTorsion.lean`). -/
theorem weilPairingElt_pow_eq_one_of_gS_three_baseField (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0)
    (htors : torsionPoint hT + torsionPoint hT + torsionPoint hT = 0)
    {f g : W.FunctionField} {u : W.CoordinateRingˣ} {n : ℕ} (hg : g ≠ 0)
    (hu : (u : W.CoordinateRing) • g ^ n = mulByThreeEndo h2 h3 f) :
    weilPairingElt hT g ^ n = 1 :=
  weilPairingElt_pow_eq_one_of_gS_three_torsion hT h2 h3
    (translatePoint_add_add_self hT htors) hg hu

end CoordinateRing

end WeierstrassCurve.Affine
