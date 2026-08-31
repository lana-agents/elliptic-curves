/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.CoordinateRingNormalGeneral
import EllipticCurves.FunctionField.NthRootOfPullbackN
import EllipticCurves.FunctionField.WeilPairingGaloisRootHprin
import EllipticCurves.FunctionField.WeilPairingTranslationSlotHprinN

/-!
# Galois equivariance of the Weil pairing at an ARBITRARY `n` (rung 6, Galois slot)

`EllipticCurves.FunctionField.WeilPairingGaloisRoot` (`#456` deliverable 2) proves

```
σ⋆(e_n(S, T)) = e_n(σS, σT)
```

from rung-5 data, at `n = 2` and `n = 3`.  This file proves it at **every** `n`, and assembles the
two headlines that produce the rung-5 data from `hprin`.

## ⚠️ This family is NOT a numeral strip, and the detector cannot see why

Of the inputs to `weilPairingElt_galois_of_gS_two`, four are already general — the engine
`weilPairingElt_galois_of_divisor_eq`, the transport `divisor_eq_equivMapDomain_of_smul_pow` (whose
endomorphism `Φ` *and* index `n` are both parameters), `divisor_eq_equivMapDomain_of_eq_single`, and
`mulByTwoEndo_algebraMap_base ↝ mulByNEndo_algebraMap_base`.  The fifth is
`galoisFunctionField_mulByTwoEndo`, and it **does not transcribe**:
`EllipticCurves.FunctionField.GaloisFunctionField` proves it, and its `[3]∗` mirror, from the
**division-polynomial coordinates** of `[2]` and `[3]` (`galoisFunctionField_Φ_eval`, `_Ψ₂Sq_eval`,
`_ΨSq_eval`, `_preΨ₄_eval`, `_preΨ_eval`, `_ψ_evalEval`).  `mulByNEndo` has **no coordinate
formula** — it comes from the group law on the generic point (`#1165`), not from `Φₙ/ΨSqₙ` — so that
route is closed at general `n` and stays closed until `#404`.

## The second route, which needs no `ωₙ`

`mulByNEndo n hn` is pinned by where it sends the two generators, and `functionField_ringHom_ext`
(`MulByNPullback`) says two ring endomorphisms of `F(W)` agreeing on `algebraMap F`, `genX` and
`genY` are equal.  `σ⋆` fixes `genX` and `genY`.  So the whole commutation reduces to

```
σ⋆ ((n • 𝒫).xCoord) = (n • 𝒫).xCoord            (and the `yCoord` twin),
```

which is not a coordinate identity at all but a **group** one: `σ⋆` acts on `(W ⁄ F(W⁄F)).Point` as
an additive automorphism, it fixes `𝒫` because it fixes both coordinates, and an additive map fixing
`𝒫` fixes `n • 𝒫`.

⚠️ **The transport hazard `GaloisFunctionField`'s module docstring warns about does not arise
here**, because `W.baseChange (W⁄F).FunctionField` and
`(W⁄F).map (algebraMap F (W⁄F).FunctionField)` are `rfl`-equal.  So Mathlib's
`WeierstrassCurve.Affine.Point.map`, which wants an `S`-algebra homomorphism, lands *literally* on
the type the generic-point stack uses, with no `Eq.mpr` and no `▸`.  This is the trick
`genPointHom` (`TranslationDoublingCommGeneral`) plays for `F`-algebra endomorphisms; what is new is
that `σ⋆` is only an `S`-algebra map, and that is enough.

## Main statements

* `WeierstrassCurve.Affine.CoordinateRing.galoisPointHom` — the action of `σ⋆` on
  `(W ⁄ F(W⁄F)).Point`, as an `AddMonoidHom`; `…_genericPoint` says it fixes `𝒫`.
* `WeierstrassCurve.Affine.CoordinateRing.galoisFunctionField_mulByNEndo` — **the new brick**:
  `σ⋆ ∘ [n]∗ = [n]∗ ∘ σ⋆` at every `n`.
* `WeierstrassCurve.Affine.CoordinateRing.weilPairingElt_galois_of_gS_n` and
  `…weilPairingMu_galois_of_gS_n` — `#456` deliverable 2 at every `n`, from rung-5 data.
* `WeierstrassCurve.Affine.exists_weilPairingElt_galois_n_of_hprin` and
  `…exists_weilPairingMu_galois_n_of_hprin` — the general-`n` forms of
  `EllipticCurves.FunctionField.WeilPairingGaloisRootHprin`'s `_two` / `_three` headlines, with the
  rung-5 data produced from `hprin` at both `S` and `σS`.
* `…exists_weilPairing{Elt,Mu}_galois_of_smooth_of_hprin` — the same with the non-constancy
  hypothesis discharged at every `3`-smooth `n ≠ 0`.  ⚠️ The first index they do **not** reach is
  `n = 5`, for `exists_gS_of_smooth`'s reason: the argument manufactures no new prime.

⚠️ **Placement.**  The substrate is here and not in `GaloisFunctionField`, which sits *below* the
whole Weil-pairing front and does not import the generic-point stack; moving it down would put
`MulByNPullback` underneath every one of that file's consumers.  This is `#1317`'s trade, for
`#1317`'s reason.

## ⚠️ What is NOT here, and why it cannot be

`exists_weilPairingElt_galois_two` / `…_three` — the **unconditional** headlines over an
algebraically closed base field — have **no general-`n` form**, and this file does not pretend
otherwise.  Their bodies call `exists_gS_two_of_isAlgClosed` (`#791`), which discharges `hprin` over
`F̄`; at general `n` there is no such producer (`exists_gS_n` and `exists_gS_of_smooth` both still
carry `hprin`).  Discharging `hprin` produces a *witness*, and `#899`'s test says witnesses do not
descend.  So everything general below carries `hprin`, exactly as `#1308`'s and `#1317`'s headlines
do.

Out of scope: any edit to `WeilPairingGaloisRoot` or `GaloisFunctionField`; the alternating and
antisymmetry families, which `#1317` showed are gated on `#899` rather than on a numeral; `ωₙ`
(`#404`), Ward (`#260`), rung 4, `#251`.

## Recovery, and Non-vacuity

`RecoveryHprin` and `Recovery` derive **all eight** merged `_two` / `_three` statements of this
family — the four `weilPairing{Elt,Mu}_galois_of_gS_*` of `WeilPairingGaloisRoot` and the four
`exists_weilPairing{Elt,Mu}_galois_*_of_hprin` of `WeilPairingGaloisRootHprin` — from the general
forms, through `mulByNEndo_two` / `mulByNEndo_three`.  Every one of the eight statements is its
merged twin **verbatim**, binders included; that is what certifies the generalisation is faithful
rather than merely similar, and the elaborator checks it so no reader has to.

`Nonvacuity` instantiates the `3`-smooth corollaries at **`n = 4`**, an index no merged Galois
statement reaches, on `y² = x³ − x` over `ℚ` — `WeilPairingGaloisRootHprin`'s own certificate curve
and base field, chosen there because `ℚ` is *not* algebraically closed.  ⚠️ `hprin` remains a
hypothesis, exactly as at `n = 2, 3`, and `ℚ ≃ₐ[ℚ] ℚ` is trivial, so the certificates say nothing
about a nontrivial Galois action; that content is carried by the general statements, over an
arbitrary extension.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.1(d).
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S}

/-! ### `σ⋆` as a map of points of `W ⁄ F(W⁄F)` -/

/-- **`σ⋆` as an `S`-algebra endomorphism of `F(W⁄F)`.**  `galoisFunctionField σ` is σ-semilinear
over `F` and therefore not an `F`-algebra map, but `σ` fixes the image of `algebraMap S F`, so it
*is* an `S`-algebra map — which is exactly what Mathlib's `Point.map` asks for. -/
noncomputable def galoisFunctionFieldAlgHom (σ : F ≃ₐ[S] F) :
    (W⁄F).FunctionField →ₐ[S] (W⁄F).FunctionField where
  toRingHom := (galoisFunctionField (W := W) σ : (W⁄F).FunctionField →+* (W⁄F).FunctionField)
  commutes' := by
    intro s
    rw [IsScalarTower.algebraMap_apply S F (W⁄F).FunctionField]
    change galoisFunctionField σ (algebraMap F (W⁄F).FunctionField (algebraMap S F s)) = _
    rw [galoisFunctionField_algebraMap, σ.commutes,
      ← IsScalarTower.algebraMap_apply S F (W⁄F).FunctionField]

/-- `σ⋆` carries points of `W ⁄ F(W⁄F)` to points of `W ⁄ F(W⁄F)`: the curve is `σ⋆`-stable
(`galoisFunctionField_curve_stable`) and `σ⋆` is injective. -/
lemma nonsingular_galoisFunctionField (σ : F ≃ₐ[S] F) {x y : (W⁄F).FunctionField}
    (h : ((W⁄F).map (algebraMap F (W⁄F).FunctionField)).Nonsingular x y) :
    ((W⁄F).map (algebraMap F (W⁄F).FunctionField)).Nonsingular
      (galoisFunctionField σ x) (galoisFunctionField σ y) := by
  have key := (((W⁄F).map (algebraMap F (W⁄F).FunctionField)).map_nonsingular
    (f := (galoisFunctionField (W := W) σ : (W⁄F).FunctionField →+* (W⁄F).FunctionField))
    (galoisFunctionField (W := W) σ).injective x y).mpr h
  rwa [galoisFunctionField_curve_stable] at key

/-- **The action of `σ⋆` on `(W ⁄ F(W⁄F)).Point`, as an `AddMonoidHom`.**  Mathlib's
`WeierstrassCurve.Affine.Point.map` for the `S`-algebra map `galoisFunctionFieldAlgHom σ`.  Being
additive is the whole content: it is what lets `σ⋆` be pushed through `n • 𝒫`.

⚠️ No transport is needed, because `W.baseChange (W⁄F).FunctionField` and
`(W⁄F).map (algebraMap F (W⁄F).FunctionField)` are `rfl`-equal. -/
noncomputable def galoisPointHom (σ : F ≃ₐ[S] F) :
    ((W⁄F).map (algebraMap F (W⁄F).FunctionField)).Point →+
      ((W⁄F).map (algebraMap F (W⁄F).FunctionField)).Point :=
  Point.map (W' := W) (galoisFunctionFieldAlgHom σ)

/-- `galoisPointHom` acts on an affine point by applying `σ⋆` to both coordinates. -/
lemma galoisPointHom_some (σ : F ≃ₐ[S] F) {x y : (W⁄F).FunctionField}
    (h : ((W⁄F).map (algebraMap F (W⁄F).FunctionField)).Nonsingular x y) :
    galoisPointHom σ (Point.some x y h)
      = Point.some (galoisFunctionField σ x) (galoisFunctionField σ y)
          (nonsingular_galoisFunctionField σ h) := rfl

variable [W.IsElliptic]

/-- **`σ⋆` fixes the generic point**, because it fixes both of its coordinates
(`galoisFunctionField_genX`, `_genY`).

⚠️ `rw [Point.some.injEq]` fails here: the two curve expressions are definitionally equal only at
`default` transparency, and `rw` elaborates at `instances`.  `congr 1` does the job, proof
irrelevance closing the `Nonsingular` component. -/
lemma galoisPointHom_genericPoint (σ : F ≃ₐ[S] F) :
    galoisPointHom σ (genericPoint (W := W⁄F)) = genericPoint (W := W⁄F) := by
  rw [genericPoint, galoisPointHom_some]
  congr 1
  · exact galoisFunctionField_genX σ
  · exact galoisFunctionField_genY σ

/-- **`σ⋆` fixes the `x`-coordinate of `n • 𝒫`, at every `n`.**  `galoisPointHom` is additive and
fixes `𝒫`, so it fixes `n • 𝒫`; the coordinates then match by injectivity of `Point.some`.  At the
point at infinity both sides are `0`. -/
lemma galoisFunctionField_xCoord_nsmul (σ : F ≃ₐ[S] F) (n : ℕ) :
    galoisFunctionField σ ((n • genericPoint (W := W⁄F)).xCoord)
      = (n • genericPoint (W := W⁄F)).xCoord := by
  have h : galoisPointHom σ (n • genericPoint (W := W⁄F)) = n • genericPoint (W := W⁄F) := by
    rw [map_nsmul, galoisPointHom_genericPoint]
  cases hc : (n • genericPoint (W := W⁄F)) with
  | zero => exact map_zero _
  | some x y hns =>
      rw [hc, galoisPointHom_some] at h
      exact (Point.some.inj h).1

/-- **`σ⋆` fixes the `y`-coordinate of `n • 𝒫`, at every `n`.**  The `yCoord` twin of
`galoisFunctionField_xCoord_nsmul`. -/
lemma galoisFunctionField_yCoord_nsmul (σ : F ≃ₐ[S] F) (n : ℕ) :
    galoisFunctionField σ ((n • genericPoint (W := W⁄F)).yCoord)
      = (n • genericPoint (W := W⁄F)).yCoord := by
  have h : galoisPointHom σ (n • genericPoint (W := W⁄F)) = n • genericPoint (W := W⁄F) := by
    rw [map_nsmul, galoisPointHom_genericPoint]
  cases hc : (n • genericPoint (W := W⁄F)) with
  | zero => exact map_zero _
  | some x y hns =>
      rw [hc, galoisPointHom_some] at h
      exact (Point.some.inj h).2

/-! ### The new brick: `σ⋆ ∘ [n]∗ = [n]∗ ∘ σ⋆` -/

/-- **Equivariance of the multiplication-by-`n` endomorphism, at every `n`.**  The general-`n` form
of `galoisFunctionField_mulByTwoEndo` and `_mulByThreeEndo`, and the only input to the Galois slot
of rung 6 that was missing at general `n`.

There is no point-shift, exactly as at `n = 2, 3`: `[n]∗` is defined by the group law on the generic
point, whose coordinates `σ⋆` fixes.  ⚠️ The proof route is *not* the merged one — see the module
docstring: the division-polynomial coordinates of `[n]` do not exist, and `galoisPointHom` replaces
them. -/
theorem galoisFunctionField_mulByNEndo (σ : F ≃ₐ[S] F) (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W⁄F)).xCoord)
    (z : (W⁄F).FunctionField) :
    galoisFunctionField σ (mulByNEndo n hn z)
      = mulByNEndo n hn (galoisFunctionField σ z) := by
  have key : (galoisFunctionField (W := W) σ :
        (W⁄F).FunctionField →+* (W⁄F).FunctionField).comp (mulByNEndo n hn)
      = (mulByNEndo n hn).comp
          (galoisFunctionField (W := W) σ : (W⁄F).FunctionField →+* (W⁄F).FunctionField) := by
    refine functionField_ringHom_ext (fun c => ?_) ?_ ?_
    · simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, mulByNEndo_algebraMap_base,
        galoisFunctionField_algebraMap]
    · simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, mulByNEndo_genX,
        galoisFunctionField_genX, galoisFunctionField_xCoord_nsmul]
    · simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, mulByNEndo_genY,
        galoisFunctionField_genY, galoisFunctionField_yCoord_nsmul]
  have := RingHom.congr_fun key z
  simpa only [RingHom.comp_apply, RingEquiv.coe_toRingHom] using this

/-! ### `#456` deliverable 2 at an arbitrary `n`, from rung-5 data -/

variable {x₂ y₂ x y : F}

/-- **Galois-equivariance of the Weil-pairing element at an arbitrary `n`, from rung-5 data.**

`σ⋆(e_n(S, T)) = e_n(σS, σT)`, where the divisor-slot roots `g` at `S` and `g'` at `σS` are given by
the rung-5 relations `u · g ^ n = [n]∗ f` and `u' · g' ^ n = [n]∗ f'` over `div f = n·(S)` and
`div f' = n·(σS)`.

`weilPairingElt_galois_of_gS_two` with the numeral removed: the two `[n]∗`-specific inputs become
`mulByNEndo_algebraMap_base` and `galoisFunctionField_mulByNEndo`, and everything else was already
general.  Nothing beyond rung 5 is carried, and in particular the rung-4-gated identity
`div g = [n]∗(S)` is not used. -/
theorem weilPairingElt_galois_of_gS_n (σ : F ≃ₐ[S] F) (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W⁄F)).xCoord) (hnz : n ≠ 0)
    (h₂ : (W⁄F).Equation x₂ y₂) (h : (W⁄F).Equation x y)
    {f f' g g' : (W⁄F).FunctionField} (hg : g ≠ 0) (hg' : g' ≠ 0)
    (hf : divisor (W⁄F) f = Finsupp.single (pointClosedPoint h) (n : ℤ))
    (hf' : divisor (W⁄F) f'
      = Finsupp.single (pointClosedPoint (equation_algEquiv σ h)) (n : ℤ))
    {u u' : (W⁄F).CoordinateRingˣ}
    (hu : (u : (W⁄F).CoordinateRing) • g ^ n = mulByNEndo n hn f)
    (hu' : (u' : (W⁄F).CoordinateRing) • g' ^ n = mulByNEndo n hn f') :
    galoisFunctionField σ (weilPairingElt h₂ g)
      = weilPairingElt (equation_algEquiv σ h₂) g' :=
  weilPairingElt_galois_of_divisor_eq σ h₂ hg hg'
    (divisor_eq_equivMapDomain_of_smul_pow σ (mulByNEndo_algebraMap_base n hn)
      (galoisFunctionField_mulByNEndo σ n hn) hnz hg hg' hu hu'
      (divisor_eq_equivMapDomain_of_eq_single σ h hf hf'))

open Classical in
/-- **Galois-equivariance of the Weil pairing in `μ_k(F)` at an arbitrary `n`, from rung-5 data.**
`weilPairingElt_galois_of_gS_n` in the honest value group of the pairing.

⚠️ The `k` of `μ_k(F)` is the order of the pairing value and is unrelated to the `n` of the rung-5
relation; it arrives with the two hypotheses `hpow`, `hpow'` and is not constrained here.  That is
the merged arrangement (`weilPairingMu_galois_of_gS_two` calls its exponent `n` while the isogeny is
`2`), preserved. -/
theorem weilPairingMu_galois_of_gS_n (σ : F ≃ₐ[S] F) (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W⁄F)).xCoord) (hnz : n ≠ 0)
    (h₂ : (W⁄F).Equation x₂ y₂) (h : (W⁄F).Equation x y)
    {f f' g g' : (W⁄F).FunctionField} {k : ℕ} [NeZero k] (hg : g ≠ 0) (hg' : g' ≠ 0)
    (hf : divisor (W⁄F) f = Finsupp.single (pointClosedPoint h) (n : ℤ))
    (hf' : divisor (W⁄F) f'
      = Finsupp.single (pointClosedPoint (equation_algEquiv σ h)) (n : ℤ))
    {u u' : (W⁄F).CoordinateRingˣ}
    (hu : (u : (W⁄F).CoordinateRing) • g ^ n = mulByNEndo n hn f)
    (hu' : (u' : (W⁄F).CoordinateRing) • g' ^ n = mulByNEndo n hn f')
    (hpow : weilPairingElt h₂ g ^ k = 1)
    (hpow' : weilPairingElt (equation_algEquiv σ h₂) g' ^ k = 1) :
    restrictRootsOfUnity (σ.toRingEquiv.toRingHom) k (weilPairingMu h₂ hpow)
      = weilPairingMu (equation_algEquiv σ h₂) hpow' :=
  weilPairingMu_galois_of_divisor_eq σ h₂ hg hg'
    (divisor_eq_equivMapDomain_of_smul_pow σ (mulByNEndo_algebraMap_base n hn)
      (galoisFunctionField_mulByNEndo σ n hn) hnz hg hg' hu hu'
      (divisor_eq_equivMapDomain_of_eq_single σ h hf hf')) hpow hpow'

end CoordinateRing

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S} [W.IsElliptic]
variable {x₂ y₂ x y : F}

open CoordinateRing

/-! ### The rung-5 data produced from `hprin`, at an arbitrary `n` -/

open Classical in
/-- **Galois-equivariance of the Weil-pairing element at an arbitrary `n`, with `hprin` the only
gate.**  `exists_weilPairingElt_galois_two`'s envelope at every `n`, with the rung-5 data produced
by `exists_gS_n` (`#1304`) rather than by `exists_gS_two_of_isAlgClosed`.

⚠️ **`hprin` is quantified over the point**, because the producer is called at `S` *and* at `σS` —
`#912`'s shape (`EllipticCurves.FunctionField.WeilPairingDivisorSlotBilinearHprin`), not `#913`'s
point-local one (`EllipticCurves.FunctionField.WeilPairingTranslationSlotHprin`).  It is forced
rather than chosen: `exists_gS_n`'s own `hprin` names `pointClosedPoint h.1` for the point it is
applied at, so a `hprin` bound to one point cannot serve both.
`EllipticCurves.FunctionField.WeilPairingGaloisRootHprin` records the same choice at `n = 2, 3`.
`σS` is again a nonsingular affine `n`-torsion point, by `nonsingular_algEquiv` and
`Point.mem_torsion_galois_smul_some`, **the latter already general in `n`**; the merged `n = 3`
docstring says so outright.

⚠️ The rung-5 data is returned rather than discarded, for the merged statements' reason:
`weilPairingElt` takes the root `g` as an argument, so a consumer with its own root should use
`weilPairingElt_galois_of_gS_n` and feed it in.  The two roots are otherwise unrelated, and `g'` is
emphatically *not* `σ⋆ g` — the constant relating them is exactly what the pairing quotient
cancels. -/
theorem exists_weilPairingElt_galois_n_of_hprin (σ : F ≃ₐ[S] F) {n : ℕ}
    (hn : Transcendental F (n • genericPoint (W := W⁄F)).xCoord) (hnz : n ≠ 0)
    (h₂ : (W⁄F).Equation x₂ y₂) (h : (W⁄F).Nonsingular x y)
    (hS : Point.some x y h ∈ (W⁄F).torsion n)
    (hprin : ∀ {x₀ y₀ : F} (h₀ : (W⁄F).Nonsingular x₀ y₀),
      Point.some x₀ y₀ h₀ ∈ (W⁄F).torsion n →
      ∀ f : (W⁄F).FunctionField, f ≠ 0 →
        divisor (W⁄F) f = Finsupp.single (pointClosedPoint h₀.left) (n : ℤ) →
        ∃ g₀ : (W⁄F).FunctionField, g₀ ≠ 0 ∧
          n • divisor (W⁄F) g₀ = divisor (W⁄F) (mulByNEndo n hn f)) :
    ∃ g g' : (W⁄F).FunctionField, g ≠ 0 ∧ g' ≠ 0 ∧
      (∃ f : (W⁄F).FunctionField, f ≠ 0 ∧
        divisor (W⁄F) f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) ∧
        ∃ u : (W⁄F).CoordinateRingˣ,
          (u : (W⁄F).CoordinateRing) • g ^ n = mulByNEndo n hn f) ∧
      (∃ f' : (W⁄F).FunctionField, f' ≠ 0 ∧
        divisor (W⁄F) f'
          = Finsupp.single (pointClosedPoint (equation_algEquiv σ h.left)) (n : ℤ) ∧
        ∃ u' : (W⁄F).CoordinateRingˣ,
          (u' : (W⁄F).CoordinateRing) • g' ^ n = mulByNEndo n hn f') ∧
      galoisFunctionField σ (weilPairingElt h₂ g)
        = weilPairingElt (equation_algEquiv σ h₂) g' := by
  obtain ⟨f, hf, hfdiv, g, hg, u, hu⟩ := exists_gS_n hn h hS (hprin h hS)
  obtain ⟨f', hf', hf'div, g', hg', u', hu'⟩ :=
    exists_gS_n hn (nonsingular_algEquiv σ h) (Point.mem_torsion_galois_smul_some σ h hS)
      (hprin (nonsingular_algEquiv σ h) (Point.mem_torsion_galois_smul_some σ h hS))
  exact ⟨g, g', hg, hg', ⟨f, hf, hfdiv, u, hu⟩, ⟨f', hf', hf'div, u', hu'⟩,
    weilPairingElt_galois_of_gS_n σ n hn hnz h₂ h.left hg hg' hfdiv hf'div hu hu'⟩

open Classical in
/-- **Galois-equivariance of the Weil pairing in `μ_n(F)` at an arbitrary `n`, with `hprin` the only
gate.**  The `μ_n` mirror of `exists_weilPairingElt_galois_n_of_hprin`, with the two `hpow` data
**produced** rather than assumed, by `weilPairingElt_pow_eq_one_of_gS_n_torsion` (`#1308`).

⚠️ The translation point `T` must be `n`-torsion, and the `F(W⁄F)`-level headline does not ask for
that: it is about a ratio and needs no order hypothesis, whereas the value being an `n`-th root of
unity is exactly what `hm₂` buys.  That is the merged arrangement, unchanged.

⚠️ **The `σ`-side torsion is derived, not assumed** — `Point.mem_torsion_galois_smul_some` supplies
it from `hm₂`, and the resulting point is `torsionPoint (equation_algEquiv σ h₂.left)` by proof
irrelevance, so no transport lemma is needed.

⚠️ `[NeZero n]` replaces `hnz : n ≠ 0` here: `weilPairingMu` occurs in the **statement** and needs
the instance to elaborate, so it cannot be produced inside the proof.  `NeZero.ne n` recovers
`n ≠ 0`. -/
theorem exists_weilPairingMu_galois_n_of_hprin (σ : F ≃ₐ[S] F) {n : ℕ} [NeZero n]
    (hn : Transcendental F (n • genericPoint (W := W⁄F)).xCoord)
    (h₂ : (W⁄F).Nonsingular x₂ y₂) (hm₂ : Point.some x₂ y₂ h₂ ∈ (W⁄F).torsion n)
    (h : (W⁄F).Nonsingular x y) (hS : Point.some x y h ∈ (W⁄F).torsion n)
    (hprin : ∀ {x₀ y₀ : F} (h₀ : (W⁄F).Nonsingular x₀ y₀),
      Point.some x₀ y₀ h₀ ∈ (W⁄F).torsion n →
      ∀ f : (W⁄F).FunctionField, f ≠ 0 →
        divisor (W⁄F) f = Finsupp.single (pointClosedPoint h₀.left) (n : ℤ) →
        ∃ g₀ : (W⁄F).FunctionField, g₀ ≠ 0 ∧
          n • divisor (W⁄F) g₀ = divisor (W⁄F) (mulByNEndo n hn f)) :
    ∃ g g' : (W⁄F).FunctionField, g ≠ 0 ∧ g' ≠ 0 ∧
      (∃ f : (W⁄F).FunctionField, f ≠ 0 ∧
        divisor (W⁄F) f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) ∧
        ∃ u : (W⁄F).CoordinateRingˣ,
          (u : (W⁄F).CoordinateRing) • g ^ n = mulByNEndo n hn f) ∧
      (∃ f' : (W⁄F).FunctionField, f' ≠ 0 ∧
        divisor (W⁄F) f'
          = Finsupp.single (pointClosedPoint (equation_algEquiv σ h.left)) (n : ℤ) ∧
        ∃ u' : (W⁄F).CoordinateRingˣ,
          (u' : (W⁄F).CoordinateRing) • g' ^ n = mulByNEndo n hn f') ∧
      ∃ hpow : weilPairingElt h₂.left g ^ n = 1,
        ∃ hpow' : weilPairingElt (equation_algEquiv σ h₂.left) g' ^ n = 1,
          restrictRootsOfUnity (σ.toRingEquiv.toRingHom) n (weilPairingMu h₂.left hpow)
            = weilPairingMu (equation_algEquiv σ h₂.left) hpow' := by
  obtain ⟨g, g', hg, hg', ⟨f, hf, hfdiv, u, hu⟩, ⟨f', hf', hf'div, u', hu'⟩, hgal⟩ :=
    exists_weilPairingElt_galois_n_of_hprin σ hn (NeZero.ne n) h₂.left h hS hprin
  have hpow : weilPairingElt h₂.left g ^ n = 1 :=
    weilPairingElt_pow_eq_one_of_gS_n_torsion h₂.left n hn (mem_torsion_iff.mp hm₂) hg hu
  have hpow' : weilPairingElt (equation_algEquiv σ h₂.left) g' ^ n = 1 :=
    weilPairingElt_pow_eq_one_of_gS_n_torsion (equation_algEquiv σ h₂.left) n hn
      (mem_torsion_iff.mp (Point.mem_torsion_galois_smul_some σ h₂ hm₂)) hg' hu'
  exact ⟨g, g', hg, hg', ⟨f, hf, hfdiv, u, hu⟩, ⟨f', hf', hf'div, u', hu'⟩, hpow, hpow',
    weilPairingMu_galois_of_weilPairingElt σ h₂.left hgal hpow hpow'⟩

/-! ### The same at every `3`-smooth `n`, with the non-constancy hypothesis discharged -/

open Classical in
/-- **Galois-equivariance of the Weil-pairing element at every `3`-smooth `n ≠ 0`**, with `hprin`
the only hypothesis beyond the setting.  `exists_weilPairingElt_galois_n_of_hprin` with `hn`
discharged by `transcendental_xCoord_nsmul_of_smooth`.

⚠️ The first index this does **not** cover is `n = 5`, exactly as for `exists_gS_of_smooth` and for
the divisor- and translation-slot mirrors, and for the same reason: the argument manufactures no new
prime. -/
theorem exists_weilPairingElt_galois_of_smooth_of_hprin (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {n : ℕ} (hnz : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h₂ : (W⁄F).Equation x₂ y₂) (h : (W⁄F).Nonsingular x y)
    (hS : Point.some x y h ∈ (W⁄F).torsion n)
    (hprin : ∀ {x₀ y₀ : F} (h₀ : (W⁄F).Nonsingular x₀ y₀),
      Point.some x₀ y₀ h₀ ∈ (W⁄F).torsion n →
      ∀ f : (W⁄F).FunctionField, f ≠ 0 →
        divisor (W⁄F) f = Finsupp.single (pointClosedPoint h₀.left) (n : ℤ) →
        ∃ g₀ : (W⁄F).FunctionField, g₀ ≠ 0 ∧
          n • divisor (W⁄F) g₀ = divisor (W⁄F) (mulByNEndo n
            (transcendental_xCoord_nsmul_of_smooth h2 h3 hnz hfac) f)) :
    ∃ g g' : (W⁄F).FunctionField, g ≠ 0 ∧ g' ≠ 0 ∧
      (∃ f : (W⁄F).FunctionField, f ≠ 0 ∧
        divisor (W⁄F) f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) ∧
        ∃ u : (W⁄F).CoordinateRingˣ, (u : (W⁄F).CoordinateRing) • g ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hnz hfac) f) ∧
      (∃ f' : (W⁄F).FunctionField, f' ≠ 0 ∧
        divisor (W⁄F) f'
          = Finsupp.single (pointClosedPoint (equation_algEquiv σ h.left)) (n : ℤ) ∧
        ∃ u' : (W⁄F).CoordinateRingˣ, (u' : (W⁄F).CoordinateRing) • g' ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hnz hfac) f') ∧
      galoisFunctionField σ (weilPairingElt h₂ g)
        = weilPairingElt (equation_algEquiv σ h₂) g' :=
  exists_weilPairingElt_galois_n_of_hprin σ _ hnz h₂ h hS hprin

open Classical in
/-- **Galois-equivariance of the Weil pairing in `μ_n(F)` at every `3`-smooth `n ≠ 0`.**  The `μ_n`
mirror of `exists_weilPairingElt_galois_of_smooth_of_hprin`.

⚠️ `[NeZero n]` here where the `F(W⁄F)`-level sibling takes `hnz : n ≠ 0`; the reason is the
general-`n` headline's, and it is forced rather than chosen. -/
theorem exists_weilPairingMu_galois_of_smooth_of_hprin (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {n : ℕ} [NeZero n] (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h₂ : (W⁄F).Nonsingular x₂ y₂) (hm₂ : Point.some x₂ y₂ h₂ ∈ (W⁄F).torsion n)
    (h : (W⁄F).Nonsingular x y) (hS : Point.some x y h ∈ (W⁄F).torsion n)
    (hprin : ∀ {x₀ y₀ : F} (h₀ : (W⁄F).Nonsingular x₀ y₀),
      Point.some x₀ y₀ h₀ ∈ (W⁄F).torsion n →
      ∀ f : (W⁄F).FunctionField, f ≠ 0 →
        divisor (W⁄F) f = Finsupp.single (pointClosedPoint h₀.left) (n : ℤ) →
        ∃ g₀ : (W⁄F).FunctionField, g₀ ≠ 0 ∧
          n • divisor (W⁄F) g₀ = divisor (W⁄F) (mulByNEndo n
            (transcendental_xCoord_nsmul_of_smooth h2 h3 (NeZero.ne n) hfac) f)) :
    ∃ g g' : (W⁄F).FunctionField, g ≠ 0 ∧ g' ≠ 0 ∧
      (∃ f : (W⁄F).FunctionField, f ≠ 0 ∧
        divisor (W⁄F) f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) ∧
        ∃ u : (W⁄F).CoordinateRingˣ, (u : (W⁄F).CoordinateRing) • g ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 (NeZero.ne n) hfac) f) ∧
      (∃ f' : (W⁄F).FunctionField, f' ≠ 0 ∧
        divisor (W⁄F) f'
          = Finsupp.single (pointClosedPoint (equation_algEquiv σ h.left)) (n : ℤ) ∧
        ∃ u' : (W⁄F).CoordinateRingˣ, (u' : (W⁄F).CoordinateRing) • g' ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 (NeZero.ne n) hfac) f') ∧
      ∃ hpow : weilPairingElt h₂.left g ^ n = 1,
        ∃ hpow' : weilPairingElt (equation_algEquiv σ h₂.left) g' ^ n = 1,
          restrictRootsOfUnity (σ.toRingEquiv.toRingHom) n (weilPairingMu h₂.left hpow)
            = weilPairingMu (equation_algEquiv σ h₂.left) hpow' :=
  exists_weilPairingMu_galois_n_of_hprin σ _ h₂ hm₂ h hS hprin

/-! ### Recovery of the four merged `_of_hprin` headlines

⚠️ These are the direct twins of the two general headlines above:
`EllipticCurves.FunctionField.WeilPairingGaloisRootHprin` states exactly this shape at `n = 2` and
`n = 3`, `hprin` quantified over the point in exactly this way.  Each statement below is that
merged statement **verbatim** and is proved *through* the general form. -/

section RecoveryHprin

open Classical in
/-- `exists_weilPairingElt_galois_two_of_hprin`, recovered.

⚠️ `Nat.cast_ofNat` is load-bearing in **both** directions: the general form writes the divisor
coefficient as `((2 : ℕ) : ℤ)`, the merged statement as `(2 : ℤ)`.

⚠️ `hprin` is quantified over the point, so `simpa … using hprin` leaves `{x₀ y₀}` as
metavariables and reports a spurious type mismatch (`#1317`'s trap).  Introduce first. -/
private theorem exists_weilPairingElt_galois_two_of_hprin_of_general
    (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    (h₂ : (W⁄F).Equation x₂ y₂) (h : (W⁄F).Nonsingular x y)
    (hS : Point.some x y h ∈ (W⁄F).torsion 2)
    (hprin : ∀ {x₀ y₀ : F} (h₀ : (W⁄F).Nonsingular x₀ y₀),
      Point.some x₀ y₀ h₀ ∈ (W⁄F).torsion 2 →
      ∀ f : (W⁄F).FunctionField, f ≠ 0 →
        divisor (W⁄F) f = Finsupp.single (pointClosedPoint h₀.left) (2 : ℤ) →
        ∃ g₀ : (W⁄F).FunctionField, g₀ ≠ 0 ∧
          2 • divisor (W⁄F) g₀ = divisor (W⁄F) (mulByTwoEndo h2 f)) :
    ∃ g g' : (W⁄F).FunctionField, g ≠ 0 ∧ g' ≠ 0 ∧
      (∃ f : (W⁄F).FunctionField, f ≠ 0 ∧
        divisor (W⁄F) f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) ∧
        ∃ u : (W⁄F).CoordinateRingˣ,
          (u : (W⁄F).CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
      (∃ f' : (W⁄F).FunctionField, f' ≠ 0 ∧
        divisor (W⁄F) f'
          = Finsupp.single (pointClosedPoint (equation_algEquiv σ h.left)) (2 : ℤ) ∧
        ∃ u' : (W⁄F).CoordinateRingˣ,
          (u' : (W⁄F).CoordinateRing) • g' ^ 2 = mulByTwoEndo h2 f') ∧
      galoisFunctionField σ (weilPairingElt h₂ g)
        = weilPairingElt (equation_algEquiv σ h₂) g' := by
  have key := exists_weilPairingElt_galois_n_of_hprin σ
    (transcendental_xCoord_two_nsmul (W := W⁄F) h2) two_ne_zero h₂ h hS
    (by intro x₀ y₀ h₀ hm₀; simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using hprin h₀ hm₀)
  simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using key

open Classical in
/-- `exists_weilPairingElt_galois_three_of_hprin`, recovered, through `mulByNEndo_three`. -/
private theorem exists_weilPairingElt_galois_three_of_hprin_of_general
    (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (h₂ : (W⁄F).Equation x₂ y₂) (h : (W⁄F).Nonsingular x y)
    (hS : Point.some x y h ∈ (W⁄F).torsion 3)
    (hprin : ∀ {x₀ y₀ : F} (h₀ : (W⁄F).Nonsingular x₀ y₀),
      Point.some x₀ y₀ h₀ ∈ (W⁄F).torsion 3 →
      ∀ f : (W⁄F).FunctionField, f ≠ 0 →
        divisor (W⁄F) f = Finsupp.single (pointClosedPoint h₀.left) (3 : ℤ) →
        ∃ g₀ : (W⁄F).FunctionField, g₀ ≠ 0 ∧
          3 • divisor (W⁄F) g₀ = divisor (W⁄F) (mulByThreeEndo h2 h3 f)) :
    ∃ g g' : (W⁄F).FunctionField, g ≠ 0 ∧ g' ≠ 0 ∧
      (∃ f : (W⁄F).FunctionField, f ≠ 0 ∧
        divisor (W⁄F) f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) ∧
        ∃ u : (W⁄F).CoordinateRingˣ,
          (u : (W⁄F).CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) ∧
      (∃ f' : (W⁄F).FunctionField, f' ≠ 0 ∧
        divisor (W⁄F) f'
          = Finsupp.single (pointClosedPoint (equation_algEquiv σ h.left)) (3 : ℤ) ∧
        ∃ u' : (W⁄F).CoordinateRingˣ,
          (u' : (W⁄F).CoordinateRing) • g' ^ 3 = mulByThreeEndo h2 h3 f') ∧
      galoisFunctionField σ (weilPairingElt h₂ g)
        = weilPairingElt (equation_algEquiv σ h₂) g' := by
  have key := exists_weilPairingElt_galois_n_of_hprin σ
    (transcendental_xCoord_three_nsmul (W := W⁄F) h2 h3) three_ne_zero h₂ h hS
    (by intro x₀ y₀ h₀ hm₀
        simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using hprin h₀ hm₀)
  simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using key

open Classical in
/-- `exists_weilPairingMu_galois_two_of_hprin`, recovered.

⚠️ `[NeZero 2]` is synthesised rather than supplied: the general form carries it as an instance
binder because `weilPairingMu` occurs in its statement. -/
private theorem exists_weilPairingMu_galois_two_of_hprin_of_general
    (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    (h₂ : (W⁄F).Nonsingular x₂ y₂) (hm₂ : Point.some x₂ y₂ h₂ ∈ (W⁄F).torsion 2)
    (h : (W⁄F).Nonsingular x y) (hS : Point.some x y h ∈ (W⁄F).torsion 2)
    (hprin : ∀ {x₀ y₀ : F} (h₀ : (W⁄F).Nonsingular x₀ y₀),
      Point.some x₀ y₀ h₀ ∈ (W⁄F).torsion 2 →
      ∀ f : (W⁄F).FunctionField, f ≠ 0 →
        divisor (W⁄F) f = Finsupp.single (pointClosedPoint h₀.left) (2 : ℤ) →
        ∃ g₀ : (W⁄F).FunctionField, g₀ ≠ 0 ∧
          2 • divisor (W⁄F) g₀ = divisor (W⁄F) (mulByTwoEndo h2 f)) :
    ∃ g g' : (W⁄F).FunctionField, g ≠ 0 ∧ g' ≠ 0 ∧
      (∃ f : (W⁄F).FunctionField, f ≠ 0 ∧
        divisor (W⁄F) f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) ∧
        ∃ u : (W⁄F).CoordinateRingˣ,
          (u : (W⁄F).CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
      (∃ f' : (W⁄F).FunctionField, f' ≠ 0 ∧
        divisor (W⁄F) f'
          = Finsupp.single (pointClosedPoint (equation_algEquiv σ h.left)) (2 : ℤ) ∧
        ∃ u' : (W⁄F).CoordinateRingˣ,
          (u' : (W⁄F).CoordinateRing) • g' ^ 2 = mulByTwoEndo h2 f') ∧
      ∃ hpow : weilPairingElt h₂.left g ^ 2 = 1,
        ∃ hpow' : weilPairingElt (equation_algEquiv σ h₂.left) g' ^ 2 = 1,
          restrictRootsOfUnity (σ.toRingEquiv.toRingHom) 2 (weilPairingMu h₂.left hpow)
            = weilPairingMu (equation_algEquiv σ h₂.left) hpow' := by
  have key := exists_weilPairingMu_galois_n_of_hprin σ
    (transcendental_xCoord_two_nsmul (W := W⁄F) h2) h₂ hm₂ h hS
    (by intro x₀ y₀ h₀ hm₀; simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using hprin h₀ hm₀)
  simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using key

open Classical in
/-- `exists_weilPairingMu_galois_three_of_hprin`, recovered, through `mulByNEndo_three`. -/
private theorem exists_weilPairingMu_galois_three_of_hprin_of_general
    (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (h₂ : (W⁄F).Nonsingular x₂ y₂)
    (hm₂ : Point.some x₂ y₂ h₂ ∈ (W⁄F).torsion 3)
    (h : (W⁄F).Nonsingular x y) (hS : Point.some x y h ∈ (W⁄F).torsion 3)
    (hprin : ∀ {x₀ y₀ : F} (h₀ : (W⁄F).Nonsingular x₀ y₀),
      Point.some x₀ y₀ h₀ ∈ (W⁄F).torsion 3 →
      ∀ f : (W⁄F).FunctionField, f ≠ 0 →
        divisor (W⁄F) f = Finsupp.single (pointClosedPoint h₀.left) (3 : ℤ) →
        ∃ g₀ : (W⁄F).FunctionField, g₀ ≠ 0 ∧
          3 • divisor (W⁄F) g₀ = divisor (W⁄F) (mulByThreeEndo h2 h3 f)) :
    ∃ g g' : (W⁄F).FunctionField, g ≠ 0 ∧ g' ≠ 0 ∧
      (∃ f : (W⁄F).FunctionField, f ≠ 0 ∧
        divisor (W⁄F) f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) ∧
        ∃ u : (W⁄F).CoordinateRingˣ,
          (u : (W⁄F).CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) ∧
      (∃ f' : (W⁄F).FunctionField, f' ≠ 0 ∧
        divisor (W⁄F) f'
          = Finsupp.single (pointClosedPoint (equation_algEquiv σ h.left)) (3 : ℤ) ∧
        ∃ u' : (W⁄F).CoordinateRingˣ,
          (u' : (W⁄F).CoordinateRing) • g' ^ 3 = mulByThreeEndo h2 h3 f') ∧
      ∃ hpow : weilPairingElt h₂.left g ^ 3 = 1,
        ∃ hpow' : weilPairingElt (equation_algEquiv σ h₂.left) g' ^ 3 = 1,
          restrictRootsOfUnity (σ.toRingEquiv.toRingHom) 3 (weilPairingMu h₂.left hpow)
            = weilPairingMu (equation_algEquiv σ h₂.left) hpow' := by
  have key := exists_weilPairingMu_galois_n_of_hprin σ
    (transcendental_xCoord_three_nsmul (W := W⁄F) h2 h3) h₂ hm₂ h hS
    (by intro x₀ y₀ h₀ hm₀
        simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using hprin h₀ hm₀)
  simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using key

end RecoveryHprin


/-! ### Recovery of the four merged `_two` / `_three` statements

⚠️ Each statement below is its merged twin **verbatim** — binders, implicit/explicit split and
conclusion — and each is proved *through* the general form rather than re-proved.  It is the check
that separates a faithful generalisation from a new statement that merely resembles one; the
elaborator performs it, so no reader has to take *"the merged proof with the numeral removed"* on
faith.

⚠️ All four are `private`: public copies would duplicate merged names.

⚠️ Only these four are recovered.  `exists_weilPairing{Elt,Mu}_galois_{two,three}` — the
unconditional `[IsAlgClosed F]` headlines — have **no** general-`n` form, for the reason in the
module docstring, and are deliberately absent. -/

namespace CoordinateRing

section Recovery

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S} [W.IsElliptic]
variable {x₂ y₂ x y : F}

/-- `weilPairingElt_galois_of_gS_two`, recovered.

⚠️ `Nat.cast_ofNat` is not decoration: the general form writes the divisor coefficient as
`((2 : ℕ) : ℤ)` and the merged statement writes `(2 : ℤ)`, so without it the two divisor hypotheses
do not match. -/
private theorem weilPairingElt_galois_of_gS_two_of_general (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    (h₂ : (W⁄F).Equation x₂ y₂) (h : (W⁄F).Equation x y)
    {f f' g g' : (W⁄F).FunctionField} (hg : g ≠ 0) (hg' : g' ≠ 0)
    (hf : divisor (W⁄F) f = Finsupp.single (pointClosedPoint h) (2 : ℤ))
    (hf' : divisor (W⁄F) f'
      = Finsupp.single (pointClosedPoint (equation_algEquiv σ h)) (2 : ℤ))
    {u u' : (W⁄F).CoordinateRingˣ}
    (hu : (u : (W⁄F).CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f)
    (hu' : (u' : (W⁄F).CoordinateRing) • g' ^ 2 = mulByTwoEndo h2 f') :
    galoisFunctionField σ (weilPairingElt h₂ g)
      = weilPairingElt (equation_algEquiv σ h₂) g' :=
  weilPairingElt_galois_of_gS_n σ 2 (transcendental_xCoord_two_nsmul (W := W⁄F) h2) two_ne_zero
    h₂ h hg hg' (by simpa only [Nat.cast_ofNat] using hf)
    (by simpa only [Nat.cast_ofNat] using hf') (u := u) (u' := u')
    (by simpa only [mulByNEndo_two h2] using hu) (by simpa only [mulByNEndo_two h2] using hu')

/-- `weilPairingElt_galois_of_gS_three`, recovered, through `mulByNEndo_three`. -/
private theorem weilPairingElt_galois_of_gS_three_of_general (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (h₂ : (W⁄F).Equation x₂ y₂) (h : (W⁄F).Equation x y)
    {f f' g g' : (W⁄F).FunctionField} (hg : g ≠ 0) (hg' : g' ≠ 0)
    (hf : divisor (W⁄F) f = Finsupp.single (pointClosedPoint h) (3 : ℤ))
    (hf' : divisor (W⁄F) f'
      = Finsupp.single (pointClosedPoint (equation_algEquiv σ h)) (3 : ℤ))
    {u u' : (W⁄F).CoordinateRingˣ}
    (hu : (u : (W⁄F).CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f)
    (hu' : (u' : (W⁄F).CoordinateRing) • g' ^ 3 = mulByThreeEndo h2 h3 f') :
    galoisFunctionField σ (weilPairingElt h₂ g)
      = weilPairingElt (equation_algEquiv σ h₂) g' :=
  weilPairingElt_galois_of_gS_n σ 3 (transcendental_xCoord_three_nsmul (W := W⁄F) h2 h3)
    three_ne_zero h₂ h hg hg' (by simpa only [Nat.cast_ofNat] using hf)
    (by simpa only [Nat.cast_ofNat] using hf') (u := u) (u' := u')
    (by simpa only [mulByNEndo_three h2 h3] using hu)
    (by simpa only [mulByNEndo_three h2 h3] using hu')

/-- `weilPairingMu_galois_of_gS_two`, recovered.

⚠️ The `n` here is the exponent of `μ_n(F)` and is unrelated to the isogeny index `2`; in the
general form it is the independent `k`, which is exactly why that binder had to be introduced. -/
private theorem weilPairingMu_galois_of_gS_two_of_general (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    (h₂ : (W⁄F).Equation x₂ y₂) (h : (W⁄F).Equation x y)
    {f f' g g' : (W⁄F).FunctionField} {n : ℕ} [NeZero n] (hg : g ≠ 0) (hg' : g' ≠ 0)
    (hf : divisor (W⁄F) f = Finsupp.single (pointClosedPoint h) (2 : ℤ))
    (hf' : divisor (W⁄F) f'
      = Finsupp.single (pointClosedPoint (equation_algEquiv σ h)) (2 : ℤ))
    {u u' : (W⁄F).CoordinateRingˣ}
    (hu : (u : (W⁄F).CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f)
    (hu' : (u' : (W⁄F).CoordinateRing) • g' ^ 2 = mulByTwoEndo h2 f')
    (hpow : weilPairingElt h₂ g ^ n = 1)
    (hpow' : weilPairingElt (equation_algEquiv σ h₂) g' ^ n = 1) :
    restrictRootsOfUnity (σ.toRingEquiv.toRingHom) n (weilPairingMu h₂ hpow)
      = weilPairingMu (equation_algEquiv σ h₂) hpow' :=
  weilPairingMu_galois_of_gS_n σ 2 (transcendental_xCoord_two_nsmul (W := W⁄F) h2) two_ne_zero
    h₂ h hg hg' (by simpa only [Nat.cast_ofNat] using hf)
    (by simpa only [Nat.cast_ofNat] using hf') (u := u) (u' := u')
    (by simpa only [mulByNEndo_two h2] using hu) (by simpa only [mulByNEndo_two h2] using hu')
    hpow hpow'

/-- `weilPairingMu_galois_of_gS_three`, recovered, through `mulByNEndo_three`. -/
private theorem weilPairingMu_galois_of_gS_three_of_general (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (h₂ : (W⁄F).Equation x₂ y₂) (h : (W⁄F).Equation x y)
    {f f' g g' : (W⁄F).FunctionField} {n : ℕ} [NeZero n] (hg : g ≠ 0) (hg' : g' ≠ 0)
    (hf : divisor (W⁄F) f = Finsupp.single (pointClosedPoint h) (3 : ℤ))
    (hf' : divisor (W⁄F) f'
      = Finsupp.single (pointClosedPoint (equation_algEquiv σ h)) (3 : ℤ))
    {u u' : (W⁄F).CoordinateRingˣ}
    (hu : (u : (W⁄F).CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f)
    (hu' : (u' : (W⁄F).CoordinateRing) • g' ^ 3 = mulByThreeEndo h2 h3 f')
    (hpow : weilPairingElt h₂ g ^ n = 1)
    (hpow' : weilPairingElt (equation_algEquiv σ h₂) g' ^ n = 1) :
    restrictRootsOfUnity (σ.toRingEquiv.toRingHom) n (weilPairingMu h₂ hpow)
      = weilPairingMu (equation_algEquiv σ h₂) hpow' :=
  weilPairingMu_galois_of_gS_n σ 3 (transcendental_xCoord_three_nsmul (W := W⁄F) h2 h3)
    three_ne_zero h₂ h hg hg' (by simpa only [Nat.cast_ofNat] using hf)
    (by simpa only [Nat.cast_ofNat] using hf') (u := u) (u' := u')
    (by simpa only [mulByNEndo_three h2 h3] using hu)
    (by simpa only [mulByNEndo_three h2 h3] using hu') hpow hpow'

end Recovery

end CoordinateRing

/-! ### Non-vacuity at `n = 4`

⚠️ The base field is **`ℚ`**, not an algebraic closure of it — the choice
`EllipticCurves.FunctionField.WeilPairingGaloisRootHprin`'s own certificates make, and for its
reason: the `[IsAlgClosed F]` twins in `WeilPairingGaloisRoot` would certify *those* statements
rather than these.  What is new here is the **index**: `n = 4` is reached by no merged Galois
statement, `_of_hprin` or unconditional.

⚠️ `hprin` remains a hypothesis, exactly as it does at `n = 2, 3`.  What these certificates
establish is that every *other* hypothesis — `3`-smoothness at a composite index, the elliptic
instance, non-singularity, `n`-torsion, and the `S`-automorphism — is inhabited outside `{2, 3}`.
⚠️ Over `ℚ` the group `ℚ ≃ₐ[ℚ] ℚ` is trivial, so these say nothing about a nontrivial Galois action;
the merged certificates have the same shape and the same limitation, and the general statements
above are the ones that carry the content over an arbitrary extension. -/

section Nonvacuity

/-- The curve `y² = x³ − x` over `ℚ`, of discriminant `64`. -/
private noncomputable def exampleCurve : Affine ℚ := ⟨0, 0, 0, -1, 0⟩

/-- ⚠️ The base field is `ℚ` itself, **not** an algebraic closure of it. -/
private abbrev exampleField : Type := ℚ

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleTwo : (2 : exampleField) ≠ 0 := by norm_num

private lemma exampleThree : (3 : exampleField) ≠ 0 := by norm_num

/-- `4` is `3`-smooth.  ⚠️ Not `by decide`: the `Decidable` instance for the bounded quantifier over
`primeFactors` gets stuck (`#1213`).  This is `NthRootOfPullbackN`'s `primeFactors_four` idiom. -/
private lemma primeFactorsFour : ∀ p ∈ (4 : ℕ).primeFactors, p = 2 ∨ p = 3 := by
  intro p hp
  obtain ⟨hpp, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
  rw [show (4 : ℕ) = 2 ^ 2 from rfl] at hdvd
  exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow hdvd))

/-- `S = (0, 0)` lies on the base-changed curve and is nonsingular. -/
private lemma exampleNonsingular : (exampleCurve⁄exampleField).Nonsingular 0 0 :=
  (exampleCurve⁄exampleField).equation_iff_nonsingular.mp (by
    simp [exampleCurve, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `S = (0, 0)` is `2`-torsion: `2y + a₁x + a₃ = 0` reads `0 = 0`. -/
private lemma exampleTorsionTwo :
    Point.some (0 : exampleField) 0 exampleNonsingular ∈ (exampleCurve⁄exampleField).torsion 2 :=
  (mem_torsion_two_some_iff exampleNonsingular).mpr (by simp [exampleCurve])

open Classical in
/-- `S = (0, 0)` is `4`-torsion because it is `2`-torsion: `4 • X = 2 • (2 • X)`. -/
private lemma exampleTorsionFour :
    Point.some (0 : exampleField) 0 exampleNonsingular ∈ (exampleCurve⁄exampleField).torsion 4 := by
  rw [mem_torsion_iff, show (4 : ℕ) = 2 * 2 from rfl, mul_nsmul,
    mem_torsion_iff.mp exampleTorsionTwo, smul_zero]

open Classical in
/-- **Galois-equivariance of the Weil-pairing element applies at `n = 4`**, on a named curve over a
base field that is not algebraically closed, with `hprin` the only hypothesis left standing.

⚠️ The conclusion is the headline's, written out in full rather than `obtain`ed and projected —
`#916` had to repair four blocks that dropped the rung-5 conjuncts and so stated something provable
with a trivial term.

⚠️ **Every `by convert` is load-bearing.**  `ℚ` has a genuine `DecidableEq` instance, so anything
stated over `ℚ` is indexed by `instDecidableEqRat`, while the headline — stated for a general `F`
under `open Classical in` — is indexed by `Classical.propDecidable`.  The objects are
propositionally but not syntactically equal and `convert` closes each gap by `Subsingleton.elim`. -/
example (σ : exampleField ≃ₐ[ℚ] exampleField) {x₂ y₂ : exampleField}
    (h₂ : (exampleCurve⁄exampleField).Equation x₂ y₂)
    (hprin : ∀ {x₀ y₀ : exampleField} (h₀ : (exampleCurve⁄exampleField).Nonsingular x₀ y₀),
      Point.some x₀ y₀ h₀ ∈ (exampleCurve⁄exampleField).torsion 4 →
      ∀ f : (exampleCurve⁄exampleField).FunctionField, f ≠ 0 →
        divisor (exampleCurve⁄exampleField) f
            = Finsupp.single (pointClosedPoint h₀.left) (4 : ℤ) →
        ∃ g₀ : (exampleCurve⁄exampleField).FunctionField, g₀ ≠ 0 ∧
          4 • divisor (exampleCurve⁄exampleField) g₀
            = divisor (exampleCurve⁄exampleField) (mulByNEndo 4
                (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree (by norm_num)
                  primeFactorsFour) f)) :
    ∃ g g' : (exampleCurve⁄exampleField).FunctionField, g ≠ 0 ∧ g' ≠ 0 ∧
      (∃ f : (exampleCurve⁄exampleField).FunctionField, f ≠ 0 ∧
        divisor (exampleCurve⁄exampleField) f
          = Finsupp.single (pointClosedPoint exampleNonsingular.left) (4 : ℤ) ∧
        ∃ u : (exampleCurve⁄exampleField).CoordinateRingˣ,
          (u : (exampleCurve⁄exampleField).CoordinateRing) • g ^ 4
            = mulByNEndo 4 (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree
                (by norm_num) primeFactorsFour) f) ∧
      (∃ f' : (exampleCurve⁄exampleField).FunctionField, f' ≠ 0 ∧
        divisor (exampleCurve⁄exampleField) f'
          = Finsupp.single
              (pointClosedPoint (equation_algEquiv σ exampleNonsingular.left)) (4 : ℤ) ∧
        ∃ u' : (exampleCurve⁄exampleField).CoordinateRingˣ,
          (u' : (exampleCurve⁄exampleField).CoordinateRing) • g' ^ 4
            = mulByNEndo 4 (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree
                (by norm_num) primeFactorsFour) f') ∧
      galoisFunctionField σ (weilPairingElt h₂ g)
        = weilPairingElt (equation_algEquiv σ h₂) g' :=
  exists_weilPairingElt_galois_of_smooth_of_hprin σ exampleTwo exampleThree (n := 4) (by norm_num)
    primeFactorsFour h₂ exampleNonsingular (by convert exampleTorsionFour)
    (fun h₀ hm₀ => hprin h₀ (by convert hm₀))

open Classical in
/-- **The `μ_4(ℚ)`-valued form applies at `n = 4` too**, with the two `hpow` data produced rather
than assumed.  The translation point is `(0, 0)` again, which is legitimate: the headline allows
`T = S`, and `#861`'s arrangement makes no independence demand. -/
example (σ : exampleField ≃ₐ[ℚ] exampleField)
    (hprin : ∀ {x₀ y₀ : exampleField} (h₀ : (exampleCurve⁄exampleField).Nonsingular x₀ y₀),
      Point.some x₀ y₀ h₀ ∈ (exampleCurve⁄exampleField).torsion 4 →
      ∀ f : (exampleCurve⁄exampleField).FunctionField, f ≠ 0 →
        divisor (exampleCurve⁄exampleField) f
            = Finsupp.single (pointClosedPoint h₀.left) (4 : ℤ) →
        ∃ g₀ : (exampleCurve⁄exampleField).FunctionField, g₀ ≠ 0 ∧
          4 • divisor (exampleCurve⁄exampleField) g₀
            = divisor (exampleCurve⁄exampleField) (mulByNEndo 4
                (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree (by norm_num)
                  primeFactorsFour) f)) :
    ∃ g g' : (exampleCurve⁄exampleField).FunctionField, g ≠ 0 ∧ g' ≠ 0 ∧
      (∃ f : (exampleCurve⁄exampleField).FunctionField, f ≠ 0 ∧
        divisor (exampleCurve⁄exampleField) f
          = Finsupp.single (pointClosedPoint exampleNonsingular.left) (4 : ℤ) ∧
        ∃ u : (exampleCurve⁄exampleField).CoordinateRingˣ,
          (u : (exampleCurve⁄exampleField).CoordinateRing) • g ^ 4
            = mulByNEndo 4 (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree
                (by norm_num) primeFactorsFour) f) ∧
      (∃ f' : (exampleCurve⁄exampleField).FunctionField, f' ≠ 0 ∧
        divisor (exampleCurve⁄exampleField) f'
          = Finsupp.single
              (pointClosedPoint (equation_algEquiv σ exampleNonsingular.left)) (4 : ℤ) ∧
        ∃ u' : (exampleCurve⁄exampleField).CoordinateRingˣ,
          (u' : (exampleCurve⁄exampleField).CoordinateRing) • g' ^ 4
            = mulByNEndo 4 (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree
                (by norm_num) primeFactorsFour) f') ∧
      ∃ hpow : weilPairingElt exampleNonsingular.left g ^ 4 = 1,
        ∃ hpow' : weilPairingElt
            (equation_algEquiv σ exampleNonsingular.left) g' ^ 4 = 1,
          restrictRootsOfUnity (σ.toRingEquiv.toRingHom) 4
              (weilPairingMu exampleNonsingular.left hpow)
            = weilPairingMu (equation_algEquiv σ exampleNonsingular.left) hpow' :=
  exists_weilPairingMu_galois_of_smooth_of_hprin σ exampleTwo exampleThree (n := 4)
    primeFactorsFour exampleNonsingular (by convert exampleTorsionFour) exampleNonsingular
    (by convert exampleTorsionFour) (fun h₀ hm₀ => hprin h₀ (by convert hm₀))

end Nonvacuity

end WeierstrassCurve.Affine
