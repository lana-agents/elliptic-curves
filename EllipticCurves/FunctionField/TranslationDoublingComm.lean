/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.GenericDoubling
import EllipticCurves.FunctionField.TranslationComposition
import EllipticCurves.FunctionField.WeilPairing

/-!
# Discharging `hcomm` for the `n = 2` Weil-pairing element from a torsion hypothesis

Let `W` be an elliptic curve over a field `F` of characteristic `≠ 2`, with a fixed affine point
`T = (xT, yT)` on `W` (`hT : W.Equation xT yT`).  The rung-6 Weil-pairing element
(`FunctionField/WeilPairing.lean`, #419) still carries the commuting hypothesis

```
hcomm : translateEndo hT ([2]∗ f) = [2]∗ f       -- [2]∗ = mulByTwoEndo, i.e. [2](P + T) = [2]P
```

This file discharges `hcomm` for `n = 2` from the clean group-theoretic hypothesis that `T` is a
`2`-torsion point (in the base-changed group `(W ⁄ F(W)).Point`):

```
htors : translatePoint hT + translatePoint hT = 0.
```

## Main results

* `translateEndo_mulByTwoEndo_gen` — the two generator identities
  `translateEndo hT (mulByTwoEndo h2 (genX W)) = mulByTwoEndo h2 (genX W)` and the `genY` analogue;
* `translateEndo_mulByTwoEndo_comp` — the operator identity
  `translateEndo hT ∘ mulByTwoEndo h2 = mulByTwoEndo h2`;
* `translateEndo_mulByTwoEndo_apply` — its applied form
  `translateEndo hT (mulByTwoEndo h2 f) = mulByTwoEndo h2 f` for every `f : F(W)`;
* `weilPairingElt_pow_eq_one_of_gS_torsion` — `e_2(S, T) ^ n = 1`, with `hcomm` discharged and only
  the torsion hypothesis `htors` remaining.

## The route (no new ring computation)

Reading `translateEndo hT` as `+ 𝒯` (`genericPoint_add_translatePoint`) and `mulByTwoEndo h2` as the
group double `𝒫 ↦ 𝒫 + 𝒫` (`genericPoint_add_self`), the commuting identity on the generic point is
the group calculation

```
(𝒫 + 𝒯) + (𝒫 + 𝒯) = (𝒫 + 𝒫) + (𝒯 + 𝒯) = 𝒫 + 𝒫      (using 𝒯 + 𝒯 = 0).
```

Since `𝒫 + 𝒫 ≠ 0` (`some_ne_zero` on `genericPoint_add_self`), `𝒫 + 𝒯` is not `2`-torsion, so
doubling it takes the tangent branch (`add_self_of_Y_ne`), whose coordinates match the doubling
coordinates of `𝒫 + 𝒫`.  Naturality of `addX`/`addY`/`slope` under `translateEndo`
(`translateEndo_addX`/`_addY`/`_slope`) then upgrades the coordinate identities to the generator
identities, and the fraction-field/`AdjoinRoot` ext (mirroring `translateEndo_comp`) upgrades those
to the full operator identity.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.
-/

open Polynomial

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic] {xT yT : F}

open Classical in
/-- **The generator identities for `translateEndo hT ∘ mulByTwoEndo h2` from `2`-torsion.**  For a
`2`-torsion point `T` (`htors : translatePoint hT + translatePoint hT = 0`), the translation `+ 𝒯`
fixes the doubling images of the coordinate generators:

```
translateEndo hT (mulByTwoEndo h2 (genX W)) = mulByTwoEndo h2 (genX W)      (and the genY analogue).
```

The proof reads both sides in the group `(W ⁄ F(W)).Point`: `(𝒫 + 𝒯) + (𝒫 + 𝒯) = 𝒫 + 𝒫` (the group
double of `𝒫 + 𝒯`, using `𝒯 + 𝒯 = 0`); `𝒫 + 𝒯` is not `2`-torsion (else `𝒫 + 𝒫 = 0`, contradicting
`some_ne_zero`), so the double takes the tangent branch whose coordinates are the doubling
coordinates of `𝒫 + 𝒫`; naturality of `addX`/`addY`/`slope` under `translateEndo` finishes. -/
theorem translateEndo_mulByTwoEndo_gen (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0)
    (htors : translatePoint hT + translatePoint hT = 0) :
    translateEndo hT (mulByTwoEndo h2 (genX W)) = mulByTwoEndo h2 (genX W)
      ∧ translateEndo hT (mulByTwoEndo h2 (genY W)) = mulByTwoEndo h2 (genY W) := by
  -- STEP 1: the group double of `𝒫 + 𝒯` is `𝒫 + 𝒫`.
  have hstep1 : (genericPoint + translatePoint hT) + (genericPoint + translatePoint hT)
      = genericPoint + genericPoint := by
    rw [add_add_add_comm, htors, add_zero]
  -- STEP 2: `𝒫 + 𝒯` is not `2`-torsion.
  have hYne : translateEndo hT (genY W)
      ≠ (W.map (algebraMap F W.FunctionField)).negY (translateEndo hT (genX W))
          (translateEndo hT (genY W)) := by
    intro hy
    have hAA : (genericPoint + translatePoint hT) + (genericPoint + translatePoint hT) = 0 := by
      rw [genericPoint_add_translatePoint hT]
      exact Point.add_self_of_Y_eq hy
    rw [hstep1, genericPoint_add_self h2] at hAA
    exact Point.some_ne_zero _ hAA
  -- STEP 3: coordinate identities from the tangent branch.
  rw [genericPoint_add_translatePoint hT, Point.add_self_of_Y_ne hYne, genericPoint_add_self h2,
    Point.some.injEq] at hstep1
  obtain ⟨hX, hY⟩ := hstep1
  -- STEP 4: push `translateEndo` inside via naturality of `addX`/`addY`/`slope`.
  refine ⟨?_, ?_⟩
  · have key : translateEndo hT (mulByTwoEndo h2 (genX W))
        = (W.map (algebraMap F W.FunctionField)).addX (translateEndo hT (genX W))
            (translateEndo hT (genX W))
            ((W.map (algebraMap F W.FunctionField)).slope (translateEndo hT (genX W))
              (translateEndo hT (genX W)) (translateEndo hT (genY W))
              (translateEndo hT (genY W))) := by
      rw [← addX_gen_eq_mulByTwo h2, translateEndo_addX, translateEndo_slope]
    rw [key]
    exact hX
  · have key : translateEndo hT (mulByTwoEndo h2 (genY W))
        = (W.map (algebraMap F W.FunctionField)).addY (translateEndo hT (genX W))
            (translateEndo hT (genX W)) (translateEndo hT (genY W))
            ((W.map (algebraMap F W.FunctionField)).slope (translateEndo hT (genX W))
              (translateEndo hT (genX W)) (translateEndo hT (genY W))
              (translateEndo hT (genY W))) := by
      rw [← addY_gen_eq_mulByTwo h2, translateEndo_addY, translateEndo_slope]
    rw [key]
    exact hY

/-- **The operator identity `translateEndo hT ∘ mulByTwoEndo h2 = mulByTwoEndo h2`**, from
`2`-torsion.  Mirrors `translateEndo_comp`: the two homomorphisms agree on `F(W)` iff they agree on
the coordinate
ring `F[W]` (`IsFractionRing.ringHom_ext`), which by `AdjoinRoot.ringHom_ext` reduces to the
constants (both fix `algebraMap F F(W) c`) and the two generators `mk W (C X)` and
`AdjoinRoot.root W.polynomial` — exactly the generator identities of
`translateEndo_mulByTwoEndo_gen`. -/
theorem translateEndo_mulByTwoEndo_comp (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0)
    (htors : translatePoint hT + translatePoint hT = 0) :
    (translateEndo hT).comp (mulByTwoEndo h2) = mulByTwoEndo h2 := by
  obtain ⟨hx, hy⟩ := translateEndo_mulByTwoEndo_gen hT h2 htors
  -- Reduce to agreement on the coordinate ring, then to the two generators.
  have hcr : (translateEndo hT).comp (mulByTwoCoordHom h2) = mulByTwoCoordHom h2 := by
    refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun c => ?_) ?_) ?_
    · -- constants: both sides reduce to `algebraMap F F(W) c`
      have hofC : AdjoinRoot.of W.polynomial (C c) = algebraMap F W.CoordinateRing c := by
        rw [IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing, AdjoinRoot.algebraMap_eq,
          ← Polynomial.C_eq_algebraMap]
      simp only [RingHom.comp_apply, hofC, mulByTwoCoordHom_algebraMap,
        translateEndo_algebraMap_base]
    · -- the `X`-generator: this is `hx`, read through `genX = algebraMap _ _ (mk (C X))`
      have hxc : translateEndo hT (mulByTwoCoordHom h2 (mk W (C X)))
          = mulByTwoCoordHom h2 (mk W (C X)) := by
        rw [genX, genPsi, mulByTwoEndo_algebraMap] at hx
        exact hx
      simpa only [RingHom.comp_apply,
        show AdjoinRoot.of W.polynomial X = mk W (C X) from rfl] using hxc
    · -- the root generator: this is `hy`, read through `genY = algebraMap _ _ root`
      have hyc : translateEndo hT (mulByTwoCoordHom h2 (AdjoinRoot.root W.polynomial))
          = mulByTwoCoordHom h2 (AdjoinRoot.root W.polynomial) := by
        rw [genY, genPsi, mulByTwoEndo_algebraMap] at hy
        exact hy
      simpa only [RingHom.comp_apply] using hyc
  refine IsFractionRing.ringHom_ext (A := W.CoordinateRing) (fun a => ?_)
  rw [RingHom.comp_apply, mulByTwoEndo_algebraMap]
  exact congr($hcr a)

/-- **The operator identity in applied form.** For every `f : F(W)`,
`translateEndo hT (mulByTwoEndo h2 f) = mulByTwoEndo h2 f`; this is the `hcomm` input consumed by
the rung-6 Weil-pairing element, discharged from the `2`-torsion hypothesis `htors`. -/
theorem translateEndo_mulByTwoEndo_apply (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0)
    (htors : translatePoint hT + translatePoint hT = 0) (f : W.FunctionField) :
    translateEndo hT (mulByTwoEndo h2 f) = mulByTwoEndo h2 f := by
  have h := translateEndo_mulByTwoEndo_comp hT h2 htors
  exact congr($h f)

/-- **`e_2(S, T) ^ n = 1` with `hcomm` discharged from `2`-torsion.**  Combines
`weilPairingElt_pow_eq_one_of_gS'` (which reduces the `n`-th-root-of-unity property to the commuting
identity `hcomm`) with `translateEndo_mulByTwoEndo_apply` (which discharges `hcomm` for the doubling
map `[2]∗ = mulByTwoEndo` from the `2`-torsion hypothesis `htors`). -/
theorem weilPairingElt_pow_eq_one_of_gS_torsion (hT : W.Equation xT yT) (h2 : (2 : F) ≠ 0)
    (htors : translatePoint hT + translatePoint hT = 0)
    {f g : W.FunctionField} {u : W.CoordinateRingˣ} {n : ℕ} (hg : g ≠ 0)
    (hu : (u : W.CoordinateRing) • g ^ n = mulByTwoEndo h2 f) :
    weilPairingElt hT g ^ n = 1 :=
  weilPairingElt_pow_eq_one_of_gS' hT h2 hg hu (translateEndo_mulByTwoEndo_apply hT h2 htors f)

end CoordinateRing

end WeierstrassCurve.Affine
