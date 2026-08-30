/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.TranslationPlaceAtInfinity

/-!
# Translation acts on the rational points of the projective curve by translation

`EllipticCurves.FunctionField.TranslationPlaceAtInfinity` identifies the permutation
`mapProjPoint W (translateAlgEquiv h_S)` of `ProjPoint W` at the point at infinity:

```lean
mapProjPoint W (translateAlgEquiv h_S) none = some (pointClosedPoint h_{-S})
mapProjPoint W (translateAlgEquiv h_S) (some (pointClosedPoint h_S)) = none
```

This file identifies it at every *affine* `F`-point: if `R ⊕ S = P` then

```lean
mapProjPoint W (translateAlgEquiv h_S) (some (pointClosedPoint h_P)) = some (pointClosedPoint h_R)
```

i.e. `τ_S` moves a point `P` to `P ⊖ S`.  Together the two statements determine the permutation on
the whole **rational** locus `{O} ∪ {affine F-points}` of `ProjPoint W`: `p ↦ p ⊖ S`, with the
sanity check that the point at infinity, read as `O`, goes to `O ⊖ S = -S`.

## Why the direction is `P ⊖ S`

`placeOf (mapProjPoint W σ p) = (placeOf W p).comap σ.symm` (`Places`), and `σ.symm` for
`σ = translateAlgEquiv h_S` is `translateEndo h_{-S}`, i.e. `f ↦ f (· ⊖ S)`.  So the transported
place consists of the `f` with `f (· ⊖ S)` regular at `P`, which are the `f` regular at `P ⊖ S`.

## The route: the group law, not an evaluation computation

The obvious attack is an evaluation-composition lemma — "translating by `S` and then evaluating at
`P` is evaluating at `P ⊕ S`" — followed by a three-way case split (secant / tangent / vertical) on
the position of `P` relative to `S`.  That is unnecessary, and in this development it does not even
typecheck: `translateCoordHom h_S : F[W] →+* F(W)` lands in the *function field*, not in `F[W]`, so
there is no composite `evalEvalHom h_P ∘ translateCoordHom h_S` to state.  (The codomain has to be
`F(W)`: the translate of a regular function has poles along the translate of the divisor of
infinity.)

Instead everything comes from the group structure of the action, at no computational cost:

* `some (pointClosedPoint h_P) = mapProjPoint W (translateAlgEquiv h_{-P}) none` — the closed point
  of `P` is already in the orbit of the point at infinity, by the merged identification at `-P`;
* `mapProjPointHom` is a monoid homomorphism (`Places`), so composing permutations is composing
  automorphisms;
* `translateAlgEquiv` turns the group law into that composition (`translateAlgEquiv_mul`, the
  `AlgEquiv` repackaging of the merged `translateEndo_comp`).

Hence `τ_S (P) = τ_S (τ_{-P} (O)) = τ_{S ⊖ P} (O) = -(S ⊖ P) = P ⊖ S`, and the degenerate cases of
the addition law never appear: the only group-law input is the relation `hsum` itself.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.eq_of_pointClosedPoint_eq` — distinct affine points cut
  out distinct closed points (the non-vacuity backbone: without it the statement below could be
  vacuously symmetric).  `EllipticCurves.FunctionField.GaloisClosedPoint` has the same fact under
  the name `pointClosedPoint_inj`, but only for a base-changed curve `W⁄F`; the statement here is
  for an arbitrary `W : Affine F`, hence the different name.  ⚠️ It **used to carry**
  `[IsDedekindDomain W.CoordinateRing]`, which was dead — the instance occurred in neither the
  remainder of its type nor its proof term, measured on the elaborated environment at `2e44940`
  (`#1272`) — so the binder is gone and the statement holds for an arbitrary coordinate ring.  Its
  proof is `XYIdeal_inj` against `pointClosedPoint_asIdeal` and nothing else;
* `WeierstrassCurve.Affine.CoordinateRing.translateAlgEquiv_mul` — `τ_P ∘ τ_Q = τ_R` whenever
  `P ⊕ Q = R`, as automorphisms;
* **`WeierstrassCurve.Affine.mapProjPoint_translateAlgEquiv_pointClosedPoint_affine`** — the
  identification;
* `WeierstrassCurve.Affine.mapProjPoint_translateAlgEquiv_pointClosedPoint_ne_self` — `τ_S` has no
  fixed point among the affine points, the sharpened non-vacuity certificate;
* `WeierstrassCurve.Affine.divisorProj_translateEndo_pointClosedPoint_affine` — the payoff, one line
  from `EllipticCurves.FunctionField.PlaceOrder`'s abstract transport.

## Implementation notes

The group relation is taken in the form `translatePoint h_R + translatePoint h_S = translatePoint
h_P`, an identity of constant points of `W ⁄ F(W)`, exactly as the merged `translateEndo_comp` takes
it.  `CoordinateRing.translatePoint_add`
(`EllipticCurves.FunctionField.WeilPairingBilinearBaseField`) converts an `F`-level relation
`torsionPoint h_R + torsionPoint h_S = torsionPoint h_P` into this form; that file is deliberately
not imported here, to keep this one a leaf of the translation subtree rather than a consumer of the
Weil-pairing stack.

## What is *not* here

* The permutation at a closed point that is **not** the closed point of an `F`-rational affine
  point.  `ProjPoint W` is all of `Option (HeightOneSpectrum F[W])`, and a height-one prime with a
  nontrivial residue extension has no `P ⊖ S` to be sent to in these terms; describing the action
  there needs closed points of `W` over an extension, which this tree does not have.  So the
  permutation is determined on the rational locus, not on `ProjPoint W`.
* The degenerate relation `R ⊕ S = O`, i.e. `P = O`: that is the merged
  `mapProjPoint_translateAlgEquiv_none`, and it cannot be stated in this signature (`h_P` ranges
  over affine points).
* The other degenerate relation, `R = O`, i.e. `P = S`: that is the merged
  `mapProjPoint_translateAlgEquiv_pointClosedPoint`, and it cannot be stated here either, for the
  same reason — its value is the point at infinity, not the closed point of an affine point.
* Anything about `[n]∗`, Riemann–Roch, or the Weil pairing itself.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.3, III.4.
-/

open Polynomial IsDedekindDomain

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

/-! ### Distinct affine points cut out distinct closed points -/

section Separation

variable {x y : F}

/-- Evaluating the coordinate-ring generator `X - x'` at a point `(x, y)` of `W`. -/
lemma evalEvalHom_XClass_eq (h : W.Equation x y) (x' : F) :
    evalEvalHom h (XClass W x') = x - x' := by
  change evalEvalHom h (mk W (C (X - C x'))) = x - x'
  rw [evalEvalHom_mk, evalEval_C]
  simp

/-- Evaluating the coordinate-ring generator `Y - y'` at a point `(x, y)` of `W`. -/
lemma evalEvalHom_YClass_eq (h : W.Equation x y) (y' : F) :
    evalEvalHom h (YClass W (C y')) = y - y' := by
  change evalEvalHom h (mk W (Y - C (C y'))) = y - y'
  rw [evalEvalHom_mk]
  simp [Polynomial.evalEval]

/-- **Distinct affine points cut out distinct ideals.**  If `⟨X - x, Y - y⟩ = ⟨X - x', Y - y'⟩` for
two points of `W`, then the points coincide: the two generators of the right-hand ideal lie in
`ker (evalEvalHom h)`, where they evaluate to `x - x'` and `y - y'`. -/
theorem XYIdeal_inj {x' y' : F} (h : W.Equation x y)
    (hEq : XYIdeal W x (C y) = XYIdeal W x' (C y')) : x = x' ∧ y = y' := by
  have hX : XClass W x' ∈ XYIdeal W x (C y) := by
    rw [hEq, XYIdeal]; exact Ideal.subset_span (Set.mem_insert _ _)
  have hY : YClass W (C y') ∈ XYIdeal W x (C y) := by
    rw [hEq, XYIdeal]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  rw [← ker_evalEvalHom h, RingHom.mem_ker, evalEvalHom_XClass_eq] at hX
  rw [← ker_evalEvalHom h, RingHom.mem_ker, evalEvalHom_YClass_eq] at hY
  exact ⟨sub_eq_zero.mp hX, sub_eq_zero.mp hY⟩

/-- **The point-to-closed-point map is injective.**  Without this, a statement of the form
"`τ_S` sends the closed point of `P` to the closed point of `R`" would carry no information: the two
closed points could coincide for trivial reasons. -/
theorem eq_of_pointClosedPoint_eq {x' y' : F}
    (h : W.Equation x y) (h' : W.Equation x' y')
    (hEq : pointClosedPoint h = pointClosedPoint h') : x = x' ∧ y = y' :=
  XYIdeal_inj h (by
    simpa only [pointClosedPoint_asIdeal] using congrArg HeightOneSpectrum.asIdeal hEq)

end Separation

/-! ### The composition law, as automorphisms -/

section Composition

variable [W.IsElliptic] {x₂ y₂ : F}

/-- The constant point `𝒯_T` of an affine point `T` is not the zero of `(W ⁄ F(W)).Point`. -/
lemma translatePoint_ne_zero (h₂ : W.Equation x₂ y₂) : translatePoint h₂ ≠ 0 :=
  Point.some_ne_zero _

/-- **The composition law for `translateAlgEquiv`.**  For affine points `P`, `Q`, `R` with
`P ⊕ Q = R` (as the constant-point identity `𝒯_P + 𝒯_Q = 𝒯_R` over `F(W)`),
`τ_P * τ_Q = τ_R` in `Aut_F F(W)`.

This is the merged `translateEndo_comp` repackaged at the type where `mapProjPointHom` can consume
it: the multiplication of `AlgEquiv`s is composition, so a monoid homomorphism out of `Aut_F F(W)`
turns this into a statement about composing the induced permutations. -/
theorem translateAlgEquiv_mul {xP yP xQ yQ xR yR : F}
    (hP : W.Equation xP yP) (hQ : W.Equation xQ yQ) (hR : W.Equation xR yR)
    (hsum : translatePoint hP + translatePoint hQ = translatePoint hR) :
    translateAlgEquiv hP * translateAlgEquiv hQ = translateAlgEquiv hR :=
  AlgEquiv.ext fun g => by
    change translateEndo hP (translateEndo hQ g) = translateEndo hR g
    exact translateEndo_translateEndo_apply hP hQ hR hsum g

end Composition

end CoordinateRing

/-! ### The action on affine points -/

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]
  [IsDedekindDomain W.CoordinateRing] {x y : F}

/-- **Translation by `-T` sends the point at infinity to the closed point of `T`.**  The merged
`mapProjPoint_translateAlgEquiv_none` read at `-T`, with the double negation collapsed by
`negY_negY`; the form in which the closed point of an arbitrary affine point is exhibited as lying
in the orbit of the point at infinity. -/
theorem mapProjPoint_translateAlgEquiv_neg_none (h : W.Equation x y) :
    mapProjPoint W (translateAlgEquiv ((W.equation_neg x y).mpr h)) none
      = some (pointClosedPoint h) := by
  have key := mapProjPoint_translateAlgEquiv_none ((W.equation_neg x y).mpr h)
  have hpt : pointClosedPoint ((W.equation_neg x (W.negY x y)).mpr
      ((W.equation_neg x y).mpr h)) = pointClosedPoint h :=
    HeightOneSpectrum.ext (by simp only [pointClosedPoint_asIdeal, negY_negY])
  rwa [hpt] at key

/-- **Translation by `S` sends the closed point of `P` to the closed point of `P ⊖ S`.**

The group relation is supplied as `𝒯_R + 𝒯_S = 𝒯_P`, i.e. `R ⊕ S = P`, matching the merged
`translateEndo_comp`; `CoordinateRing.translatePoint_add` produces it from an `F`-level relation.

Proof: the closed point of `P` is `τ_{-P}` applied to the point at infinity, so the left-hand side
is `(τ_S * τ_{-P})` applied to the point at infinity, `mapProjPointHom` being a monoid
homomorphism.  The group law identifies `τ_S * τ_{-P}` with `τ_{-R}`, and `τ_{-R}` sends the point
at infinity to the closed point of `R`.  No case analysis on the position of `P` relative to `S` is
needed, and no evaluation of functions at points occurs anywhere. -/
theorem mapProjPoint_translateAlgEquiv_pointClosedPoint_affine {xP yP xS yS xR yR : F}
    (hP : W.Equation xP yP) (hS : W.Equation xS yS) (hR : W.Equation xR yR)
    (hsum : translatePoint hR + translatePoint hS = translatePoint hP) :
    mapProjPoint W (translateAlgEquiv hS) (some (pointClosedPoint hP))
      = some (pointClosedPoint hR) := by
  have hgrp : translatePoint hS + translatePoint ((W.equation_neg xP yP).mpr hP)
      = translatePoint ((W.equation_neg xR yR).mpr hR) := by
    rw [translatePoint_neg hP, translatePoint_neg hR, ← hsum, neg_add_rev, ← add_assoc,
      add_neg_cancel, zero_add]
  rw [← mapProjPoint_translateAlgEquiv_neg_none hP, ← Equiv.trans_apply, ← mapProjPoint_mul,
    translateAlgEquiv_mul hS ((W.equation_neg xP yP).mpr hP) ((W.equation_neg xR yR).mpr hR)
      hgrp, mapProjPoint_translateAlgEquiv_neg_none hR]

/-- **Translation by an affine point fixes no affine point.**  Sharpens the merged
`mapProjPoint_translateAlgEquiv_ne_one` (which exhibits a single moved point, the point at
infinity) on the affine locus, and is what makes the identification above non-vacuous: the closed
points of `P` and of `P ⊖ S` are genuinely different.

If they agreed then `P ⊖ S = P` by `eq_of_pointClosedPoint_eq`, forcing `𝒯_S = 0`, which no constant
point of an affine point is. -/
theorem mapProjPoint_translateAlgEquiv_pointClosedPoint_ne_self {xP yP xS yS xR yR : F}
    (hP : W.Equation xP yP) (hS : W.Equation xS yS) (hR : W.Equation xR yR)
    (hsum : translatePoint hR + translatePoint hS = translatePoint hP) :
    mapProjPoint W (translateAlgEquiv hS) (some (pointClosedPoint hP))
      ≠ some (pointClosedPoint hP) := by
  rw [mapProjPoint_translateAlgEquiv_pointClosedPoint_affine hP hS hR hsum]
  intro hEq
  obtain ⟨hx, hy⟩ := eq_of_pointClosedPoint_eq hR hP (Option.some.inj hEq)
  subst hx
  subst hy
  refine translatePoint_ne_zero hS (add_left_cancel (a := translatePoint hR) ?_)
  rw [add_zero]
  exact hsum

/-- **The order of vanishing of `τ_S f` at `P ⊖ S` is the order of `f` at `P`.**  The affine
counterpart of the merged `divisorProj_translateEndo_none`: the abstract transport
`divisorProj_algEquiv_apply` says the two orders agree along `mapProjPoint`, and the identification
above says which point that is. -/
theorem divisorProj_translateEndo_pointClosedPoint_affine {xP yP xS yS xR yR : F}
    (hP : W.Equation xP yP) (hS : W.Equation xS yS) (hR : W.Equation xR yR)
    (hsum : translatePoint hR + translatePoint hS = translatePoint hP)
    {f : W.FunctionField} (hf : f ≠ 0) :
    divisorProj W (translateEndo hS f) (some (pointClosedPoint hR))
      = divisorProj W f (some (pointClosedPoint hP)) := by
  have h := divisorProj_algEquiv_apply (translateAlgEquiv hS) hf (some (pointClosedPoint hP))
  rwa [mapProjPoint_translateAlgEquiv_pointClosedPoint_affine hP hS hR hsum,
    translateAlgEquiv_apply] at h

end WeierstrassCurve.Affine
