/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.WeilPairingFunctionThree
import EllipticCurves.FunctionField.WeilPairingGaloisRoot
import EllipticCurves.TateModule.GaloisAction

/-!
# Galois-equivariance of the Weil pairing as a function of two torsion points

`EllipticCurves.FunctionField.WeilPairingFunctionTwo` (`#922`) and
`EllipticCurves.FunctionField.WeilPairingFunctionThree` (`#925`) replaced the existential packaging
of rung 6 by genuine functions

```
weilPairingTwo : E[2] → E[2] → μ_2(F),      weilPairingThree : E[3] → E[3] → μ_3(F),
```

and re-read bilinearity, the alternating property, antisymmetry and non-degeneracy through them.
This file does the same for the remaining property named in `#419`, **Galois-equivariance**:

```
σ(e_n(S, T)) = e_n(σ • S, σ • T)     for σ ∈ Gal(F/S),
```

at the `F(W⁄F)` level and at the `μ_n(F)` level, at `n = 2` and `n = 3`.  ⚠️ **No new mathematics
is proved.**  The content is a case split on whether each point is `O` and one application of the
merged headline `exists_weilPairing{Elt,Mu}_galois_{two,three}`
(`EllipticCurves.FunctionField.WeilPairingGaloisRoot`, `#456`/`#830`) read through the bridge.

## Why this is an equation and the merged form is not

`exists_weilPairingMu_galois_two` returns *two rung-5 roots* — one at `S`, one at `σS` — alongside
the relation between the two pairing values, because `weilPairingElt` takes the root as an
argument.  It therefore cannot be composed: there is no term `e_2(σS, σT)` to write down.  Once the
pairing is a function of the two points, both sides name themselves and the statement is an
equation between two values of one function, so it composes with bilinearity and with
non-degeneracy.  That is the whole content of this file, and it is the same move `#922` made for
the other four properties.

## ⚠️ The action on `E[n]` was already there, and the two spellings of a `σ`-side proof are
interchangeable

`TateModule/GaloisAction` supplies `SMul (F ≃ₐ[S] F) ((W⁄F).torsion n)` and
`torsion_galois_smul_coe`, so `σ • S` needs no construction here; `GaloisPointAction`'s
`Point.galois_smul_some` is `rfl` and turns it into coordinates.  ⚠️ The merged headlines phrase
the `σ`-side hypothesis as `equation_algEquiv σ h.left` where the bridge produces
`(nonsingular_algEquiv σ h).left`.  **Both are proofs of the same `Prop`, so proof irrelevance
closes every such mismatch and no transport lemma is needed** — this is the same observation
`exists_weilPairingMu_galois_two`'s docstring records at the existential level.

⚠️ `torsion` takes `[DecidableEq F]` (`Torsion/Defs.lean`) and `TateModule/GaloisAction`'s
instances are generic in it, so `open Classical in` is enough and **no `Subsingleton.elim` bridge
is required** anywhere in this file.

## Main statements

* `WeierstrassCurve.Affine.weilPairingEltTwo_galois` / `weilPairingEltThree_galois` — the
  `F(W⁄F)`-level equations, `galoisFunctionField σ (e_n(S, T)) = e_n(σ • S, σ • T)`.
* `WeierstrassCurve.Affine.weilPairingTwo_galois` / `weilPairingThree_galois` — the same at the
  honest value group, `restrictRootsOfUnity σ n (e_n(S, T)) = e_n(σ • S, σ • T)` in `μ_n(F)`.

## ⚠️ A hypothesis asymmetry that exists upstream and disappears here

`exists_weilPairingElt_galois_two` asks nothing about the order of the translation point, whereas
`exists_weilPairingMu_galois_two` asks it to be `n`-torsion — that is what makes the pairing
*value* a root of unity, and `WeilPairingGaloisRoot`'s docstring calls it the price of "nothing
carried" at the `μ_n(F)` level.  Here **both statements take `T : (W⁄F).torsion n`**, so the
hypothesis is free on both sides (`hm₂ := hT ▸ T.2`) and the asymmetry is invisible.  Recorded
because a reader comparing the two levels upstream will expect to find it.

## Scope

⚠️ **`[IsAlgClosed F]` is load-bearing and will not lift**, for the reason recorded in both
function files: it enters through `exists_gS_{two,three}_of_isAlgClosed` (`#791`/`#825`) alone, but
that use *produces a witness*, and `#899`'s test says base change never reaches an obstruction of
that shape.  ⚠️ **A one-gate file is liftable only if the gate is also equality-shaped**; the
single-gate test and `#899`'s test are different tests.  There is no hypothesis here to weaken, so
there is no `_of_hprin` twin to write.

⚠️ **Equivariance of the bundled `weilPairingTwoHom` / `weilPairingThreeHom` is deliberately
absent.**  Any such statement would be proved from the pointwise equations below, and packaging it
is a separate question about which `MonoidHom` category the `σ`-action lives in; nothing here
prejudges it.

⚠️ This is not general `n` (which needs `#251`; ⚠️ **not** `#404`, and **not** Ward), not
`#E[n] = n²`, and not the `weilPairingElt`-level Galois statements, which are `#456` and are merged
in `WeilPairingGaloisRoot` and `WeilPairingGaloisRootHprin`.

⚠️ **`#404` is closed, and the general-`n` entry above named it as the gate.**  PR #557 proved the
on-curve identity for `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` at every index over every commutative ring —
`WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero`, `EllipticCurves.Torsion.OmegaCrux`.  What still
gates a general index is the *other* statement this tree also called `ωₙ`: the identification of
those coordinates with the **group-law** multiple `n • P`, which is `#251`.  ⚠️ The two-reading
account is `EllipticCurves.FunctionField.MulByNPullback`; the gate is relettered here, not lifted.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8, Prop. 8.1(d).
-/

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S} [W.IsElliptic]

/-! ### `n = 2` -/

section Two

variable [IsAlgClosed F]

open Classical in
/-- **Galois-equivariance of `weilPairingEltTwo`**, at the `F(W⁄F)` level:

```
σ⋆(e_2(S, T)) = e_2(σ • S, σ • T).
```

Three cases, of which two are corners.  If `T = O` or `S = O` both sides are `1`, because the
Galois action fixes `O` (`smul_zero`) and `σ⋆` fixes `1`.  Otherwise both points are affine and
`exists_weilPairingElt_galois_two` (`#456`) supplies a rung-5 root at `S` and one at `σS`; each is
read through `weilPairingEltTwo_eq_weilPairingElt`, whose divisor hypothesis is *character for
character* what that theorem returns. -/
theorem weilPairingEltTwo_galois (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0) (P T : (W⁄F).torsion 2) :
    galoisFunctionField σ (weilPairingEltTwo h2 P T)
      = weilPairingEltTwo h2 (σ • P) (σ • T) := by
  cases hT : (T : (W⁄F).Point) with
  | zero =>
      have h0 : T = 0 := Subtype.ext (hT.trans Point.zero_def.symm)
      rw [h0, smul_zero, weilPairingEltTwo_zero_right, weilPairingEltTwo_zero_right, map_one]
  | some x₂ y₂ h₂ =>
      cases hP : (P : (W⁄F).Point) with
      | zero =>
          have h0 : P = 0 := Subtype.ext hP
          rw [h0, smul_zero, weilPairingEltTwo_zero_left, weilPairingEltTwo_zero_left, map_one]
      | some x y h =>
          have hS : Point.some x y h ∈ (W⁄F).torsion 2 := hP ▸ P.2
          obtain ⟨g, g', hg0, hg0', ⟨f, hf, hfdiv, u, hu⟩, ⟨f', hf', hf'div, u', hu'⟩, hgal⟩ :=
            exists_weilPairingElt_galois_two σ h2 h₂.left h hS
          rw [weilPairingEltTwo_eq_weilPairingElt h2
                (by rw [hP]; exact isWeilRootTwo_some h2 h hg0 hf hfdiv hu) h₂ hT,
            weilPairingEltTwo_eq_weilPairingElt h2 (g := g')
                (by
                  rw [torsion_galois_smul_coe, hP, Point.galois_smul_some]
                  exact isWeilRootTwo_some h2 (nonsingular_algEquiv σ h) hg0' hf' hf'div hu')
                (nonsingular_algEquiv σ h₂)
                (by rw [torsion_galois_smul_coe, hT, Point.galois_smul_some])]
          exact hgal

open Classical in
/-- **Galois-equivariance of `weilPairingTwo`**, at the honest value group:

```
σ · e_2(S, T) = e_2(σ • S, σ • T)     in μ_2(F).
```

Same three cases as the `F(W⁄F)` form, off `exists_weilPairingMu_galois_two` and
`weilPairingTwo_eq_weilPairingMu`.  ⚠️ The translation point's `2`-torsion hypothesis, which
that theorem asks for and its `F(W⁄F)` twin does not, is free here — it is `hT ▸ T.2`. -/
theorem weilPairingTwo_galois (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0) (P T : (W⁄F).torsion 2) :
    restrictRootsOfUnity (σ.toRingEquiv.toRingHom) 2 (weilPairingTwo h2 P T)
      = weilPairingTwo h2 (σ • P) (σ • T) := by
  cases hT : (T : (W⁄F).Point) with
  | zero =>
      have h0 : T = 0 := Subtype.ext (hT.trans Point.zero_def.symm)
      rw [h0, smul_zero, weilPairingTwo_zero_right, weilPairingTwo_zero_right, map_one]
  | some x₂ y₂ h₂ =>
      have hm₂ : Point.some x₂ y₂ h₂ ∈ (W⁄F).torsion 2 := hT ▸ T.2
      cases hP : (P : (W⁄F).Point) with
      | zero =>
          have h0 : P = 0 := Subtype.ext hP
          rw [h0, smul_zero, weilPairingTwo_zero_left, weilPairingTwo_zero_left, map_one]
      | some x y h =>
          have hS : Point.some x y h ∈ (W⁄F).torsion 2 := hP ▸ P.2
          obtain ⟨g, g', hg0, hg0', ⟨f, hf, hfdiv, u, hu⟩, ⟨f', hf', hf'div, u', hu'⟩,
            hpow, hpow', hgal⟩ := exists_weilPairingMu_galois_two σ h2 h₂ hm₂ h hS
          have e1 : weilPairingTwo h2 P T = weilPairingMu h₂.left hpow :=
            weilPairingTwo_eq_weilPairingMu h2
              (by rw [hP]; exact isWeilRootTwo_some h2 h hg0 hf hfdiv hu) h₂ hT hpow
          have e2 : weilPairingTwo h2 (σ • P) (σ • T)
              = weilPairingMu (equation_algEquiv σ h₂.left) hpow' := by
            refine weilPairingTwo_eq_weilPairingMu h2 (g := g') ?_ (nonsingular_algEquiv σ h₂) ?_
              hpow'
            · rw [torsion_galois_smul_coe, hP, Point.galois_smul_some]
              exact isWeilRootTwo_some h2 (nonsingular_algEquiv σ h) hg0' hf' hf'div hu'
            · rw [torsion_galois_smul_coe, hT, Point.galois_smul_some]
          rw [e1, e2]
          exact hgal

end Two

/-! ### `n = 3` -/

section Three

variable [IsAlgClosed F]

open Classical in
/-- **Galois-equivariance of `weilPairingEltThree`**, the `n = 3` mirror of
`weilPairingEltTwo_galois`.

⚠️ A transcription, and unlike `#925`'s divisor-slot row that is checkable rather than hopeful:
**no point is added anywhere in this proof**, the only case split being *is this point `O`*, so the
`n = 2`/`n = 3` asymmetry that comes from a `2`-torsion point being its own negative cannot
arise. -/
theorem weilPairingEltThree_galois (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (P T : (W⁄F).torsion 3) :
    galoisFunctionField σ (weilPairingEltThree h2 h3 P T)
      = weilPairingEltThree h2 h3 (σ • P) (σ • T) := by
  cases hT : (T : (W⁄F).Point) with
  | zero =>
      have h0 : T = 0 := Subtype.ext (hT.trans Point.zero_def.symm)
      rw [h0, smul_zero, weilPairingEltThree_zero_right, weilPairingEltThree_zero_right, map_one]
  | some x₂ y₂ h₂ =>
      cases hP : (P : (W⁄F).Point) with
      | zero =>
          have h0 : P = 0 := Subtype.ext hP
          rw [h0, smul_zero, weilPairingEltThree_zero_left, weilPairingEltThree_zero_left, map_one]
      | some x y h =>
          have hS : Point.some x y h ∈ (W⁄F).torsion 3 := hP ▸ P.2
          obtain ⟨g, g', hg0, hg0', ⟨f, hf, hfdiv, u, hu⟩, ⟨f', hf', hf'div, u', hu'⟩, hgal⟩ :=
            exists_weilPairingElt_galois_three σ h2 h3 h₂.left h hS
          rw [weilPairingEltThree_eq_weilPairingElt h2 h3
                (by rw [hP]; exact isWeilRootThree_some h2 h3 h hg0 hf hfdiv hu) h₂ hT,
            weilPairingEltThree_eq_weilPairingElt h2 h3 (g := g')
                (by
                  rw [torsion_galois_smul_coe, hP, Point.galois_smul_some]
                  exact isWeilRootThree_some h2 h3 (nonsingular_algEquiv σ h) hg0' hf' hf'div hu')
                (nonsingular_algEquiv σ h₂)
                (by rw [torsion_galois_smul_coe, hT, Point.galois_smul_some])]
          exact hgal

open Classical in
/-- **Galois-equivariance of `weilPairingThree`** in `μ_3(F)`, the `n = 3` mirror of
`weilPairingTwo_galois`. -/
theorem weilPairingThree_galois (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (P T : (W⁄F).torsion 3) :
    restrictRootsOfUnity (σ.toRingEquiv.toRingHom) 3 (weilPairingThree h2 h3 P T)
      = weilPairingThree h2 h3 (σ • P) (σ • T) := by
  cases hT : (T : (W⁄F).Point) with
  | zero =>
      have h0 : T = 0 := Subtype.ext (hT.trans Point.zero_def.symm)
      rw [h0, smul_zero, weilPairingThree_zero_right, weilPairingThree_zero_right, map_one]
  | some x₂ y₂ h₂ =>
      have hm₂ : Point.some x₂ y₂ h₂ ∈ (W⁄F).torsion 3 := hT ▸ T.2
      cases hP : (P : (W⁄F).Point) with
      | zero =>
          have h0 : P = 0 := Subtype.ext hP
          rw [h0, smul_zero, weilPairingThree_zero_left, weilPairingThree_zero_left, map_one]
      | some x y h =>
          have hS : Point.some x y h ∈ (W⁄F).torsion 3 := hP ▸ P.2
          obtain ⟨g, g', hg0, hg0', ⟨f, hf, hfdiv, u, hu⟩, ⟨f', hf', hf'div, u', hu'⟩,
            hpow, hpow', hgal⟩ := exists_weilPairingMu_galois_three σ h2 h3 h₂ hm₂ h hS
          have e1 : weilPairingThree h2 h3 P T = weilPairingMu h₂.left hpow :=
            weilPairingThree_eq_weilPairingMu h2 h3
              (by rw [hP]; exact isWeilRootThree_some h2 h3 h hg0 hf hfdiv hu) h₂ hT hpow
          have e2 : weilPairingThree h2 h3 (σ • P) (σ • T)
              = weilPairingMu (equation_algEquiv σ h₂.left) hpow' := by
            refine weilPairingThree_eq_weilPairingMu h2 h3 (g := g') ?_
              (nonsingular_algEquiv σ h₂) ?_ hpow'
            · rw [torsion_galois_smul_coe, hP, Point.galois_smul_some]
              exact isWeilRootThree_some h2 h3 (nonsingular_algEquiv σ h) hg0' hf' hf'div hu'
            · rw [torsion_galois_smul_coe, hT, Point.galois_smul_some]
          rw [e1, e2]
          exact hgal

end Three

/-! ### Non-vacuity

⚠️ **This is one of the two fronts in this tree whose statements need *two* fields**: a base field,
an extension, and an `S`-automorphism of the extension, plus `[IsAlgClosed F]`.  The curves and
points are `WeilPairingGaloisRoot`'s own — `y² = x³ − x` at `(0, 0)` and `(1, 0)` for `n = 2`, and
`y² + y = x³` at `(0, 0)` for `n = 3`, each defined over `ℚ` and base-changed to
`AlgebraicClosure ℚ`.  ⚠️ A *second* base curve is unavoidable at `n = 3`: `y² = x³ − x` has
`Ψ₃ = 3X⁴ − 6X² − 1`, with no rational root, so none of its `3`-torsion points can be **named**.

⚠️ **`σ` is universally quantified in every certificate below, and that is a real limitation rather
than a stylistic choice.**  `AlgebraicClosure ℚ` has no non-identity automorphism this tree can
name, so no certificate here fixes a `σ`.  `WeilPairingGaloisRoot`'s block has the same shape for
the same reason.  Said plainly rather than left for a reader to notice.

⚠️ **Which certificate is load-bearing.**  The first and third are the equivariance equations at
named points; they are universally quantified in `σ`, so they certify that the construction
elaborates on a curve that exists — real, but weak (`#916`).  **The second and fourth are the ones
with weight**: they say the pairing value at two `ℚ`-*rational* torsion points is fixed by every
`σ ∈ Gal(F/ℚ)`, i.e. lies in the fixed field.  That is not an instance of any universally
quantified equation in this file — it consumes the rationality of the two points, through
`galois_smul_some_eq_some_iff` and `map_zero`/`map_one`, and it is false as stated for a general
pair of torsion points. -/

section Nonvacuity

/-! The certificate curves `y² = x³ − x` and `y² + y = x³` are the shared
`EllipticCurves.Fixture.y2EqX3SubX` and `EllipticCurves.Fixture.y2AddYEqX3`, and the base —
algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here. -/

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

/-- `S = (0, 0)` lies on the base-changed curve and is nonsingular. -/
private lemma exampleNonsingular : ((y2EqX3SubX ℚ)⁄AlgClosedQ).Nonsingular 0 0 :=
  ((y2EqX3SubX ℚ)⁄AlgClosedQ).equation_iff_nonsingular.mp (by
    simp [y2EqX3SubX, WeierstrassCurve.Affine.equation_iff])

/-- `T = (1, 0)` lies on the base-changed curve and is nonsingular. -/
private lemma exampleNonsingularTranslate : ((y2EqX3SubX ℚ)⁄AlgClosedQ).Nonsingular 1 0 :=
  ((y2EqX3SubX ℚ)⁄AlgClosedQ).equation_iff_nonsingular.mp (by
    simp [y2EqX3SubX, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `S = (0, 0)` is `2`-torsion: `2y + a₁x + a₃ = 0` reads `0 = 0`. -/
private lemma exampleTorsion :
    Point.some (0 : AlgClosedQ) 0 exampleNonsingular ∈ ((y2EqX3SubX ℚ)⁄AlgClosedQ).torsion 2 :=
  (mem_torsion_two_some_iff exampleNonsingular).mpr (by simp [y2EqX3SubX])

open Classical in
/-- `T = (1, 0)` is `2`-torsion, as at `(0, 0)`. -/
private lemma exampleTorsionTranslate :
    Point.some (1 : AlgClosedQ) 0 exampleNonsingularTranslate
      ∈ ((y2EqX3SubX ℚ)⁄AlgClosedQ).torsion 2 :=
  (mem_torsion_two_some_iff exampleNonsingularTranslate).mpr (by simp [y2EqX3SubX])

open Classical in
/-- `S = (0, 0)` as an element of `E[2]`. -/
private noncomputable def exampleS : ((y2EqX3SubX ℚ)⁄AlgClosedQ).torsion 2 :=
  ⟨Point.some 0 0 exampleNonsingular, exampleTorsion⟩

open Classical in
/-- `T = (1, 0)` as an element of `E[2]`, distinct from `exampleS`. -/
private noncomputable def exampleT : ((y2EqX3SubX ℚ)⁄AlgClosedQ).torsion 2 :=
  ⟨Point.some 1 0 exampleNonsingularTranslate, exampleTorsionTranslate⟩

open Classical in
/-- ⚠️ **`(0, 0)` is `ℚ`-rational, so every `σ ∈ Gal(F/ℚ)` fixes it.**  This is what makes the
invariance certificate below more than an instance of the equivariance equation. -/
private lemma exampleS_fixed (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) : σ • exampleS = exampleS :=
  Subtype.ext ((Point.galois_smul_some_eq_some_iff σ exampleNonsingular exampleNonsingular).mpr
    ⟨(map_zero σ).symm, (map_zero σ).symm⟩)

open Classical in
/-- `(1, 0)` is `ℚ`-rational too, so it is fixed as well. -/
private lemma exampleT_fixed (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) : σ • exampleT = exampleT :=
  Subtype.ext ((Point.galois_smul_some_eq_some_iff σ exampleNonsingularTranslate
    exampleNonsingularTranslate).mpr ⟨(map_one σ).symm, (map_zero σ).symm⟩)

open Classical in
/-- **The equivariance equation at `n = 2`, on a curve that exists, at two distinct named
`2`-torsion points.**  A schema instance: universally quantified in `σ`. -/
example (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) :
    restrictRootsOfUnity (σ.toRingEquiv.toRingHom) 2 (weilPairingTwo exampleTwo exampleS exampleT)
      = weilPairingTwo exampleTwo (σ • exampleS) (σ • exampleT) :=
  weilPairingTwo_galois σ exampleTwo exampleS exampleT

open Classical in
/-- **⚠️ The load-bearing certificate at `n = 2`: `e_2((0,0), (1,0))` is `Gal(F/ℚ)`-invariant.**

Both points are `ℚ`-rational, so `σ` fixes each of them, and equivariance then says the *value* is
fixed — it lies in the fixed field of `Gal(F/ℚ)`.  ⚠️ This is **not** an instance of any
universally quantified equation in this file: it consumes `exampleS_fixed` and `exampleT_fixed`,
which are statements about *these* two points and false for a general pair. -/
example (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) :
    restrictRootsOfUnity (σ.toRingEquiv.toRingHom) 2 (weilPairingTwo exampleTwo exampleS exampleT)
      = weilPairingTwo exampleTwo exampleS exampleT := by
  rw [weilPairingTwo_galois σ exampleTwo exampleS exampleT, exampleS_fixed, exampleT_fixed]

/-- `S = (0, 0)` lies on the base-changed curve `y² + y = x³` and is nonsingular. -/
private lemma exampleNonsingularThree : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).Nonsingular 0 0 :=
  ((y2AddYEqX3 ℚ)⁄AlgClosedQ).equation_iff_nonsingular.mp (by
    simp [y2AddYEqX3, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `S = (0, 0)` is `3`-torsion: `Ψ₃ = 3X⁴ + 3b₆X` vanishes at `0`. -/
private lemma exampleTorsionThree :
    Point.some (0 : AlgClosedQ) 0 exampleNonsingularThree
      ∈ ((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3 :=
  mem_torsion_three_some_iff'.mpr (by
    simp [y2AddYEqX3, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈])

open Classical in
/-- `S = (0, 0)` as an element of `E[3]`. -/
private noncomputable def exampleSThree : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3 :=
  ⟨Point.some 0 0 exampleNonsingularThree, exampleTorsionThree⟩

open Classical in
/-- `(0, 0)` is `ℚ`-rational on `y² + y = x³` too. -/
private lemma exampleSThree_fixed (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) :
    σ • exampleSThree = exampleSThree :=
  Subtype.ext ((Point.galois_smul_some_eq_some_iff σ exampleNonsingularThree
    exampleNonsingularThree).mpr ⟨(map_zero σ).symm, (map_zero σ).symm⟩)

open Classical in
/-- **The equivariance equation at `n = 3`, on a curve that exists.**

⚠️ Taken at `S = T = (0, 0)`, and that is a limitation of the curve rather than of the statement:
the only nameable `3`-torsion points on `y² + y = x³` are `(0, 0)` and its negative `(0, −1)`,
since the `X = −1` fibre of `Ψ₃ = 3X(X³ + 1)` is `y² + y + 1 = 0`.  The same limitation is recorded
by `#829`/`#845`/`#855`/`WeilPairingGaloisRoot` about the same curve; at `n = 2` above there is no
such limitation and the certificate is at two distinct points. -/
example (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) :
    restrictRootsOfUnity (σ.toRingEquiv.toRingHom) 3
        (weilPairingThree exampleTwo exampleThree exampleSThree exampleSThree)
      = weilPairingThree exampleTwo exampleThree (σ • exampleSThree) (σ • exampleSThree) :=
  weilPairingThree_galois σ exampleTwo exampleThree exampleSThree exampleSThree

open Classical in
/-- **⚠️ The load-bearing certificate at `n = 3`**, the mirror of the `n = 2` one: the value at the
`ℚ`-rational `3`-torsion point `(0, 0)` is `Gal(F/ℚ)`-invariant, and the proof consumes the
rationality of that point rather than only the equivariance equation. -/
example (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) :
    restrictRootsOfUnity (σ.toRingEquiv.toRingHom) 3
        (weilPairingThree exampleTwo exampleThree exampleSThree exampleSThree)
      = weilPairingThree exampleTwo exampleThree exampleSThree exampleSThree := by
  rw [weilPairingThree_galois σ exampleTwo exampleThree exampleSThree exampleSThree,
    exampleSThree_fixed]

open Classical in
/-- **The `F(W⁄F)`-level equation at `n = 2`, on the same curve**, so that both levels of this file
are certified and not only the value-group one. -/
example (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) :
    galoisFunctionField σ (weilPairingEltTwo exampleTwo exampleS exampleT)
      = weilPairingEltTwo exampleTwo exampleS exampleT := by
  rw [weilPairingEltTwo_galois σ exampleTwo exampleS exampleT, exampleS_fixed, exampleT_fixed]

open Classical in
/-- **The `F(W⁄F)`-level equation at `n = 3`**, completing the four-way coverage. -/
example (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) :
    galoisFunctionField σ (weilPairingEltThree exampleTwo exampleThree exampleSThree exampleSThree)
      = weilPairingEltThree exampleTwo exampleThree exampleSThree exampleSThree := by
  rw [weilPairingEltThree_galois σ exampleTwo exampleThree exampleSThree exampleSThree,
    exampleSThree_fixed]

end Nonvacuity

end WeierstrassCurve.Affine
