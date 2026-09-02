/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByNTranscendence
import EllipticCurves.FunctionField.MulByTwoDegree

/-!
# `F(W)` is finite over `[n]∗F(W)`, from non-constancy alone

`EllipticCurves.FunctionField.MulByNPullback` builds `[n]∗ : F(W) →+* F(W)` for every `n` out of
the group multiple `n • 𝒫`, under the single hypothesis that `x(n • 𝒫)` is **transcendental** over
`F` — geometrically, that `[n]` is non-constant.  This file shows that the same hypothesis, and
nothing else, already gives the *finiteness* half of Silverman *AEC* II.2.4:

```
Module.Finite ([n]∗F(W)) F(W)     and     ∀ z : F(W), ([n]∗).IsIntegralElem z.
```

⚠️ **It gives no degree.**  `[F(W) : [n]∗F(W)] = n²` is a different statement and is **not** proved
here; see `## What this is not` below.

## Why this is not the merged `n = 2` route repeated

At `n = 2` the same two facts are `module_finite_mulByTwoRange` and `mulByTwoEndo_isIntegralElem`
(`EllipticCurves.FunctionField.MulByTwoExtensionFinite`,
`EllipticCurves.FunctionField.PlacePullback`), and they are reached through
`mulByTwoEndo_isIntegralElem_genX` — an **explicit monic quartic** in `genX` read off the
duplication formula `x(2P) = Φ₂/Ψ₂Sq`.  There is no such polynomial at general `n` without `ωₙ`
and the general `n` coordinate formula (`#251`), so that route does not generalise.

⚠️ **The `#404` half of that pair has been paid, and only the `#251` half remains.**  PR #557 proved
the on-curve identity for `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` at every index over every commutative ring
(`WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero`, `EllipticCurves.Torsion.OmegaCrux`).  It says
those coordinates lie on the curve; it does **not** identify them with the group-law multiple
`n • P`, which is what a written-down `Φₙ/ΨSqₙ` for `[n]` needs and is `#251`
(`WeierstrassCurve.Affine.HasXCoordFormula`, `EllipticCurves.Torsion.NsmulSurjective`, available at
`n = 2, 3` only).  ⚠️ The gate is relettered, not lifted, and `#1184` is untouched; the two-reading
account is `EllipticCurves.FunctionField.MulByNPullback`.

The route here is a transcendence-degree count and uses no coordinate formula at all.  Write
`u = φ (genX W)` for an `F`-fixing endomorphism `φ` of `F(W)`.

* `F(W)` is algebraic over `F[genX]`, because `[F(W) : F(x)] = 2` (`finrank_ratFuncRange`, `#682`'s
  bottom rung, itself unconditional) and `F(x) = F⟮genX⟯` is the fraction field of `F[genX]`.  Hence
  `trdeg F F(W) ≤ 1` (`Algebra.IsAlgebraic.trdeg_le_cardinalMk`).
* `u` transcendental over `F` makes `{u}` algebraically independent, and an algebraically
  independent set of size `≥ trdeg` is a transcendence basis
  (`AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le_of_finite`).  So `F(W)` is algebraic over
  `F⟮u⟯` — and hence over any subfield containing `F` and `u`, in particular over `φ F(W)`.
* Algebraic over a **field** is integral, which is `hφint`; and `genX` integral over `φ F(W)` makes
  `φ F(W)⟮genX⟯` finite over `φ F(W)` while `F(W)` stays finite over `φ F(W)⟮genX⟯`, since it is
  already finite over the smaller `F⟮genX⟯`.  Two steps of a tower.

## Main statements

* `WeierstrassCurve.Affine.CoordinateRing.isAlgebraic_subfield_of_transcendental` — `F(W)` is
  algebraic over any subfield containing `F` and one element transcendental over `F`;
* `WeierstrassCurve.Affine.CoordinateRing.isIntegralElem_of_transcendental` — the hypothesis
  `hφint` of `EllipticCurves.FunctionField.PlacePullback`, for any `F`-fixing endomorphism whose
  value at `genX` is transcendental;
* `WeierstrassCurve.Affine.CoordinateRing.module_finite_subfield_of_transcendental` — the same
  hypothesis makes `F(W)` a finite module over the subfield;
* `WeierstrassCurve.Affine.CoordinateRing.mulByNEndo_isIntegralElem` and
  `…module_finite_mulByNEndoFieldRange` — the two at `φ = [n]∗`;
* `…module_finite_mulByNEndoOfAlgClosedFieldRange` — the second over `F̄`, where the transcendence
  hypothesis is automatic and only `n ≠ 0` and `(2 : F) ≠ 0` remain.

## What this is *not*

⚠️ **No degree.**  `finrank_mulByTwoFieldRange` gets `[F(W) : [2]∗F(W)] = 4` from
`deg Φ₂ = 4` against `deg Ψ₂Sq = 3` and the coprimality `#681`, and `#775` gets `9` the same way at
`n = 3`.  Nothing in this file computes a `finrank`, and `[F(W) : [n]∗F(W)] = n²` at general `n`
**stays gated**.  ⚠️ This paragraph used to add *"there is no group-law substitute for that degree
count"*, and that is **false at a `3`-smooth `n`**: `#1213`
(`EllipticCurves.FunctionField.MulByNComposition`) proves `[m · n]∗ = [m]∗ ∘ [n]∗` from the group
law alone, and degrees multiply in towers, so `4` and `9` give `n²` at every `n` whose prime factors
are `2` and `3`.  The group law is exactly the substitute there; what it cannot do is manufacture a
new prime, which is why `n = 5` is untouched and the rest of this paragraph stands.  ⚠️ It is *not*
gated on
the degrees, though — `natDegree_Φ` and `natDegree_ΨSq` are **Mathlib**'s at general `n` — nor on
`x ∘ [n] ∈ F(x)`, which is `EllipticCurves.FunctionField.MulByNXCoordRatFunc`.  What is missing is
that element *written down* as the reduced fraction `Φₙ/ΨSqₙ` (`#251`), the coprimality
`IsCoprime (W.Φ n) (W.ΨSq n)` at general `n` (`#1184`), and the `(n : F) ≠ 0` that `natDegree_ΨSq`
carries and `mulByNEndo` does not; `EllipticCurves.FunctionField.MulByNPlacePullback` argues each of
them.  What generalises is that the degree is *finite*.

⚠️ **No separability.**  `Algebra.IsSeparable ([n]∗F(W)) F(W)` is what `#754` carries as a
hypothesis; in characteristic zero it follows from finiteness
(`isSeparable_mulByTwoEndoFieldRange`'s argument), and in characteristic `p` it is false for
`p ∣ n`.  Nothing here addresses it.

⚠️ **Nothing about places.**  The consumers are in
`EllipticCurves.FunctionField.MulByNPlacePullback`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.4.
-/

open Polynomial Module

open scoped IntermediateField.algebraAdjoinAdjoin

universe u

namespace RingHom

/-- **Bridge `IsIntegral` over the image subfield → `RingHom.IsIntegralElem`.**  The `fieldRange`
companion of `EllipticCurves.FunctionField.PlacePullback`'s
`isIntegralElem_of_isIntegral_range`: a monic polynomial over `f.fieldRange` killing `z` is pulled
back along the isomorphism `K ≃+* f.fieldRange` to a monic polynomial over `K` whose `f`-evaluation
kills `z`. -/
theorem isIntegralElem_of_isIntegral_fieldRange {K : Type*} [Field K] (f : K →+* K) {z : K}
    (hz : _root_.IsIntegral ↥f.fieldRange z) : f.IsIntegralElem z := by
  obtain ⟨p, hpm, hpe⟩ := hz
  refine ⟨p.map (f.rangeRestrictFieldEquiv.symm : ↥f.fieldRange →+* K), hpm.map _, ?_⟩
  have hce : f.comp (f.rangeRestrictFieldEquiv.symm : ↥f.fieldRange →+* K)
      = f.fieldRange.subtype :=
    RingHom.ext fun a => congrArg Subtype.val (f.rangeRestrictFieldEquiv.apply_symm_apply a)
  rw [Polynomial.eval₂_map, hce]
  exact hpe

end RingHom

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type u} [Field F] {W : Affine F}

/-! ### The transcendence degree of `F(W)` over `F` is at most one -/

/-- **`F(W)` is algebraic over the polynomial subring `F[genX]`.**  It is algebraic over the
subfield `F(x) = F⟮genX⟯`, because that extension has degree `2` (`finrank_ratFuncRange`), and
`F⟮genX⟯` is in turn algebraic over `F[genX]` — being its field of fractions. -/
theorem isAlgebraic_algebraAdjoin_genX :
    Algebra.IsAlgebraic ↥(Algebra.adjoin F ({genX W} : Set W.FunctionField)) W.FunctionField := by
  haveI : FiniteDimensional ↥(ratFuncRange W) W.FunctionField :=
    Module.finite_of_finrank_pos (by rw [finrank_ratFuncRange]; norm_num)
  haveI : Algebra.IsAlgebraic ↥(ratFuncRange W) W.FunctionField := Algebra.IsAlgebraic.of_finite _ _
  rw [ratFuncRange_eq_adjoin] at this
  exact Algebra.IsAlgebraic.trans ↥(Algebra.adjoin F ({genX W} : Set W.FunctionField))
    ↥(IntermediateField.adjoin F ({genX W} : Set W.FunctionField)) W.FunctionField

/-- **One transcendental element already generates `F(W)` up to algebraicity.**  `trdeg F F(W) ≤ 1`
by `isAlgebraic_algebraAdjoin_genX`, so a single algebraically independent element is a
transcendence basis and `F(W)` is algebraic over the subfield it generates.

⚠️ This is the step that replaces the explicit monic quartic of `mulByTwoEndo_isIntegralElem_genX`;
it knows nothing about the element beyond its transcendence. -/
theorem isAlgebraic_adjoin_of_transcendental {u : W.FunctionField} (hu : Transcendental F u) :
    Algebra.IsAlgebraic ↥(IntermediateField.adjoin F ({u} : Set W.FunctionField))
      W.FunctionField := by
  haveI := isAlgebraic_algebraAdjoin_genX (W := W)
  have h1 : Algebra.trdeg F W.FunctionField ≤ 1 := by
    have := Algebra.IsAlgebraic.trdeg_le_cardinalMk F ({genX W} : Set W.FunctionField)
    simpa using this
  have hind : AlgebraicIndependent F (fun _ : PUnit.{u + 1} => u) := by
    rw [algebraicIndependent_unique_type_iff]
    exact hu
  have hb : IsTranscendenceBasis F (fun _ : PUnit.{u + 1} => u) :=
    hind.isTranscendenceBasis_of_trdeg_le_of_finite (h1.trans_eq Cardinal.mk_punit.symm)
  have := hb.isAlgebraic_field
  rwa [Set.range_const] at this

/-- **`F(W)` is algebraic over any subfield that contains `F` and one transcendental element.**
The subfield contains `F⟮u⟯`, and `F(W)` is algebraic over that. -/
theorem isAlgebraic_subfield_of_transcendental {L : Subfield W.FunctionField}
    (hF : ∀ c : F, algebraMap F W.FunctionField c ∈ L)
    {u : W.FunctionField} (hu : Transcendental F u) (huL : u ∈ L) :
    Algebra.IsAlgebraic ↥L W.FunctionField := by
  haveI := isAlgebraic_adjoin_of_transcendental hu
  have hle : (IntermediateField.adjoin F ({u} : Set W.FunctionField)).toSubfield ≤ L := by
    rw [IntermediateField.adjoin_toSubfield]
    refine Subfield.closure_le.2 ?_
    rintro z (⟨c, rfl⟩ | hz)
    · exact hF c
    · rw [Set.mem_singleton_iff] at hz; subst hz; exact huL
  letI : Algebra ↥(IntermediateField.adjoin F ({u} : Set W.FunctionField)) ↥L :=
    (Subfield.inclusion hle).toAlgebra
  haveI : IsScalarTower ↥(IntermediateField.adjoin F ({u} : Set W.FunctionField)) ↥L
      W.FunctionField := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Algebra.IsAlgebraic.extendScalars
    (R := ↥(IntermediateField.adjoin F ({u} : Set W.FunctionField)))
    (Subfield.inclusion hle).injective

/-! ### Module-finiteness -/

/-- Finiteness of `F(W)` passes **up** a chain of intermediate fields: if `F(W)` is finite over the
smaller one it is finite over the larger. -/
theorem module_finite_of_intermediateField_le {E₁ E₂ : IntermediateField F W.FunctionField}
    (h : E₁ ≤ E₂) (hfin : Module.Finite ↥E₁ W.FunctionField) :
    Module.Finite ↥E₂ W.FunctionField := by
  letI : Algebra ↥E₁ ↥E₂ := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower ↥E₁ ↥E₂ W.FunctionField := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI := hfin
  exact Module.Finite.of_restrictScalars_finite ↥E₁ ↥E₂ W.FunctionField

/-- **Integrality of `genX` over an intermediate field is enough for finiteness.**  The tower is
`E ⊆ E⟮genX⟯ ⊆ F(W)`: the first step is finite because `genX` is integral, and the second because
`F(W)` is already finite over the smaller `F⟮genX⟯` (`finrank_ratFuncRange`).

⚠️ `genY` never appears.  The merged `n = 2` route needs both coordinates integral over the image
(`mulByTwoRange_isIntegral_genX`, `…_genY`) because it builds `F(W)` as `[2]∗F(W)[genX, genY]`;
here the second coordinate is carried by the merged degree-`2` bottom rung instead. -/
theorem module_finite_of_isIntegral_genX (E : IntermediateField F W.FunctionField)
    (hX : IsIntegral ↥E (genX W)) : Module.Finite ↥E W.FunctionField := by
  haveI : FiniteDimensional ↥E ↥(IntermediateField.adjoin ↥E ({genX W} : Set W.FunctionField)) :=
    IntermediateField.finiteDimensional_adjoin (fun x hx => by
      rw [Set.mem_singleton_iff] at hx; subst hx; exact hX)
  have hle : IntermediateField.adjoin F ({genX W} : Set W.FunctionField)
      ≤ (IntermediateField.adjoin ↥E ({genX W} : Set W.FunctionField)).restrictScalars F := by
    rw [IntermediateField.adjoin_le_iff]
    rintro x hx
    rw [Set.mem_singleton_iff] at hx; subst hx
    simp only [SetLike.mem_coe, IntermediateField.mem_restrictScalars]
    exact IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
  have hfinX : Module.Finite ↥(IntermediateField.adjoin F ({genX W} : Set W.FunctionField))
      W.FunctionField := by
    rw [← ratFuncRange_eq_adjoin]
    exact Module.finite_of_finrank_pos (by rw [finrank_ratFuncRange]; norm_num)
  haveI : Module.Finite ↥(IntermediateField.adjoin ↥E ({genX W} : Set W.FunctionField))
      W.FunctionField := module_finite_of_intermediateField_le hle hfinX
  exact Module.Finite.trans ↥(IntermediateField.adjoin ↥E ({genX W} : Set W.FunctionField))
    W.FunctionField

/-- **`F(W)` is a finite module over any subfield containing `F` and a transcendental element.**
This is the finiteness half of *"a non-constant map of curves is finite"* (Silverman II.2.4), with
no degree attached. -/
theorem module_finite_subfield_of_transcendental {L : Subfield W.FunctionField}
    (hF : ∀ c : F, algebraMap F W.FunctionField c ∈ L)
    {u : W.FunctionField} (hu : Transcendental F u) (huL : u ∈ L) :
    Module.Finite ↥L W.FunctionField := by
  haveI := isAlgebraic_subfield_of_transcendental hF hu huL
  exact module_finite_of_isIntegral_genX (L.toIntermediateField hF)
    (Algebra.IsIntegral.isIntegral (R := ↥L) (genX W))

/-! ### The two hypotheses of `PlacePullback`, for a general `F`-fixing endomorphism -/

variable {φ : W.FunctionField →+* W.FunctionField}

/-- **`F(W)` is integral over `φ F(W)`** — the hypothesis `hφint` of
`EllipticCurves.FunctionField.PlacePullback` — for any `F`-fixing endomorphism `φ` whose value at
`genX` is transcendental over `F`.

⚠️ `PlacePullback`'s docstring calls `hφint` *"load-bearing, not decoration"*: it is what forces the
contracted valuation subring to be proper, and it fails for an embedding whose image is a subfield
over which `F(W)` is transcendental.  Transcendence of `φ (genX W)` is exactly what rules that
out. -/
theorem isIntegralElem_of_transcendental
    (hφF : ∀ c : F, φ (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c)
    (hφX : Transcendental F (φ (genX W))) (z : W.FunctionField) : φ.IsIntegralElem z := by
  haveI := isAlgebraic_subfield_of_transcendental (L := φ.fieldRange)
    (fun c => ⟨algebraMap F W.FunctionField c, hφF c⟩) hφX ⟨genX W, rfl⟩
  exact RingHom.isIntegralElem_of_isIntegral_fieldRange φ
    (Algebra.IsIntegral.isIntegral (R := ↥φ.fieldRange) z)

/-- **`F(W)` is a finite module over `φ F(W)`**, for any `F`-fixing endomorphism `φ` whose value at
`genX` is transcendental over `F`. -/
theorem module_finite_fieldRange_of_transcendental
    (hφF : ∀ c : F, φ (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c)
    (hφX : Transcendental F (φ (genX W))) :
    Module.Finite ↥φ.fieldRange W.FunctionField :=
  module_finite_subfield_of_transcendental
    (fun c => ⟨algebraMap F W.FunctionField c, hφF c⟩) hφX ⟨genX W, rfl⟩

/-! ### The multiplication-by-`n` instantiation -/

variable [W.IsElliptic]

/-- The value of `[n]∗` at `genX` is `x(n • 𝒫)`, so its transcendence is exactly `mulByNEndo`'s own
hypothesis. -/
theorem transcendental_mulByNEndo_genX (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) :
    Transcendental F (mulByNEndo n hn (genX W)) := by
  rw [mulByNEndo_genX]; exact hn

/-- **`F(W)` is integral over `[n]∗F(W)`, for every `n` at which `[n]` is non-constant.**  This is
`mulByTwoEndo_isIntegralElem` (`EllipticCurves.FunctionField.PlacePullback`) at general `n`, and
unlike that one it consumes no division polynomial. -/
theorem mulByNEndo_isIntegralElem (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) (z : W.FunctionField) :
    (mulByNEndo n hn).IsIntegralElem z :=
  isIntegralElem_of_transcendental (mulByNEndo_algebraMap_base n hn)
    (transcendental_mulByNEndo_genX n hn) z

/-- **`F(W)` is a finite module over `[n]∗F(W)`**, for every `n` at which `[n]` is non-constant.

⚠️ **This is finiteness without a degree.**  `finrank_mulByTwoEndoFieldRange` says the degree is `4`
at `n = 2` and `#775` says it is `9` at `n = 3`; `[F(W) : [n]∗F(W)] = n²` is not proved here and is
not proved anywhere on this tree at general `n`. -/
theorem module_finite_mulByNEndoFieldRange (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) :
    Module.Finite ↥(mulByNEndo n hn).fieldRange W.FunctionField :=
  module_finite_fieldRange_of_transcendental (mulByNEndo_algebraMap_base n hn)
    (transcendental_mulByNEndo_genX n hn)

/-- **`F(W)` is a finite module over `[n]∗F(W)` over `F̄`**, for every `n ≠ 0` — the
`mulByNEndoOfAlgClosed` corollary, with no hypothesis left except `n ≠ 0` and `(2 : F) ≠ 0`.

⚠️ Still no degree.  At a **general** `n`, `[F(W) : [n]∗F(W)] = n²` needs `x ∘ [n]` written down as
`Φₙ/ΨSqₙ` (`#251`), `#1184` and `(n : F) ≠ 0`, as *"What this is not"* above records — over
`F̄` as everywhere else.  ⚠️ At a `3`-smooth `n` it needs none of them:
`EllipticCurves.FunctionField.MulByNComposition` gets it from `[m · n]∗ = [m]∗ ∘ [n]∗` and the two
merged degrees. -/
theorem module_finite_mulByNEndoOfAlgClosedFieldRange [IsAlgClosed F] (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) :
    Module.Finite ↥(mulByNEndoOfAlgClosed (W := W) h2 hn).fieldRange W.FunctionField :=
  module_finite_mulByNEndoFieldRange n _

/-! ### Consistency with the merged `n = 2` layer

⚠️ Both statements below are already merged, with different proofs: `mulByTwoEndo_isIntegralElem`
runs on the explicit monic quartic of `mulByTwoEndo_isIntegralElem_genX`, and
`module_finite_mulByTwoEndoFieldRange` runs on `finrank_mulByTwoEndoFieldRange = 4`, which needs the
coprimality `#681`.  Re-deriving them here checks that the general route's hypotheses really are
satisfied at `n = 2` — i.e. that nothing in it is a statement about general `n` that quietly fails
at the one index where the answer is known. -/

section Consistency

variable (h2 : (2 : F) ≠ 0)

include h2 in
example (z : W.FunctionField) : (mulByTwoEndo (W := W) h2).IsIntegralElem z :=
  isIntegralElem_of_transcendental (mulByTwoEndo_algebraMap_base h2)
    (by rw [← xCoord_two_nsmul_genericPoint h2]; exact transcendental_xCoord_two_nsmul h2) z

include h2 in
example : Module.Finite ↥(mulByTwoEndo (W := W) h2).fieldRange W.FunctionField :=
  module_finite_fieldRange_of_transcendental (mulByTwoEndo_algebraMap_base h2)
    (by rw [← xCoord_two_nsmul_genericPoint h2]; exact transcendental_xCoord_two_nsmul h2)

end Consistency

end CoordinateRing

end WeierstrassCurve.Affine
