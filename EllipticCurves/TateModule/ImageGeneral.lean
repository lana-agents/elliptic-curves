/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.TateModule.FreeGeneral
import EllipticCurves.TateModule.PrimaryImage

/-!
# The image of `det ρ_{E,ℓ}` is compact and closed, at EVERY prime `ℓ ≠ char F`

`EllipticCurves.TateModule.PrimaryImage` proves compactness and closedness of `range ρ_{E,ℓ}` in a
*given* basis at an arbitrary prime, and states the two basis-free consequences —
`isCompact_range_galoisDet_of_nonempty` and `isClosed_range_galoisDet_of_nonempty` — in terms of
one input: `Nonempty (T_ℓE ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])`. **This file supplies that input at every
prime `ℓ` with `(ℓ : F) ≠ 0` and contains no argument**; both proofs are one line, and the input is
`nonempty_tateModuleEquivProd_of_natCast_ne_zero` (`EllipticCurves.TateModule.FreeGeneral`, `#268`).

This is `EllipticCurves.TateModule.ImageThree`'s `isCompact_range_galoisDetThree` /
`isClosed_range_galoisDetThree` pair with `3` replaced by an arbitrary prime away from the
characteristic, and it is the `Image` entry of `#1533` item 4's list.

## ⚠️ What "image" does and does not mean here

* **Not surjectivity, not openness of the image, not Serre.** Compactness and closedness of
  `range (det ρ_{E,ℓ})` say **nothing** about which subgroup of `ℤ_[ℓ]ˣ` it is. *"The image is
  open"* is a genuinely different theorem and nothing here supplies it.
* **Not progress towards `det ρ_{E,ℓ} = χ_ℓ`.** Knowing that the image of a character is closed
  says nothing about which character it is; that identification needs the Weil pairing on `E[ℓ^k]`
  for every `k`.
* **Nothing at `ℓ = char F`**, where `T_ℓE` has rank `0` or `1` and the rank-two input does not
  exist. ⚠️ Note that closedness of a *smaller* image is not a weaker statement one could still
  hope for here — the input is what produces the basis at all.

## What this file does NOT do

* **No `def`s and no `…General` twins.** `galoisDet` and `galoisRepMatrix`
  (`EllipticCurves.TateModule.PrimaryDeterminant`, `…PrimaryMatrixRep`) already are the general-`ℓ`
  definitions, and the basis-parametrised statements of `PrimaryImage` —
  `isCompact_range_galoisRepMatrix`, `isClosed_range_galoisRepMatrix`,
  `isCompact_range_galoisDet_of_basis`, … — are already at an arbitrary prime and need nothing from
  here. Only the two basis-**free** statements had an input to supply.
* `EllipticCurves.TateModule.ImageThree` is **not** deleted: it reaches `ℓ = 3` through
  `x(3P) = Φ₃/Ψ₃²`, this file reaches every prime through `#E[n] = n²` and the Wronskian identity,
  and the `_three` names are consumed downstream.

## Main statements

* `WeierstrassCurve.Affine.isCompact_range_galoisDet_of_natCast_ne_zero`
* `WeierstrassCurve.Affine.isClosed_range_galoisDet_of_natCast_ne_zero`

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open Matrix

open scoped WeierstrassCurve.Affine.ProfiniteTopology

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
variable {ℓ : ℕ} [Fact ℓ.Prime]
variable [Algebra.IsIntegral S F] [IsGalois S F] [IsAlgClosed F] [(W'⁄F).IsElliptic]

/-- **The image of the determinant character `det ρ_{E,ℓ}` is compact**, at every prime `ℓ` with
`(ℓ : F) ≠ 0`, with no basis supplied.

⚠️ **Deletion test**, measured on this file as committed. Replacing the argument
`(tateModule.nonempty_tateModuleEquivProd_of_natCast_ne_zero h2 hl)` by a hole — `by refine
isCompact_range_galoisDet_of_nonempty (W' := W') (F := F) (ℓ := ℓ) ?_` — leaves

```
error: unsolved goals
S : Type u_1
F : Type u_2
inst✝⁸ : Field S
inst✝⁷ : Field F
inst✝⁶ : DecidableEq F
inst✝⁵ : Algebra S F
W' : Affine S
ℓ : ℕ
inst✝⁴ : Fact (Nat.Prime ℓ)
inst✝³ : Algebra.IsIntegral S F
inst✝² : IsGalois S F
inst✝¹ : IsAlgClosed F
inst✝ : WeierstrassCurve.IsElliptic W'⁄F
h2 : 2 ≠ 0
hl : ↑ℓ ≠ 0
⊢ Nonempty (↥((W'⁄F).tateModule ℓ) ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])
```

⚠️ `h2` and `hl` both **survive**, so what the deletion removes is a construction and not a
hypothesis, and the residual is a **goal**. It is `#268`'s theorem, and it is the only thing that
ever cost anything at `ℓ ≥ 5` on this front. -/
theorem isCompact_range_galoisDet_of_natCast_ne_zero (h2 : (2 : F) ≠ 0) (hl : (ℓ : F) ≠ 0) :
    IsCompact (Set.range (galoisDet (W' := W') (F := F) (ℓ := ℓ))) :=
  isCompact_range_galoisDet_of_nonempty
    (tateModule.nonempty_tateModuleEquivProd_of_natCast_ne_zero h2 hl)

/-- **The image of `det ρ_{E,ℓ}` is a closed subgroup of `ℤ_[ℓ]ˣ`**, at every prime `ℓ` with
`(ℓ : F) ≠ 0`. This is the layer `EllipticCurves.TateModule.PrimaryImageProfinite` bundles. -/
theorem isClosed_range_galoisDet_of_natCast_ne_zero (h2 : (2 : F) ≠ 0) (hl : (ℓ : F) ≠ 0) :
    IsClosed (Set.range (galoisDet (W' := W') (F := F) (ℓ := ℓ))) :=
  isClosed_range_galoisDet_of_nonempty
    (tateModule.nonempty_tateModuleEquivProd_of_natCast_ne_zero h2 hl)

/-! ### Non-vacuity

Three risks, three certificates, as in `EllipticCurves.TateModule.MatrixRepGeneral`: that the
hypotheses are simultaneously satisfiable over a base whose absolute Galois group is not trivial
(`S = ℚ`, `F = ℚ̄`); that the statement is not a re-parametrisation of `{2, 3, 5}` (hence `ℓ = 7` on
a **second** curve as well as `ℓ = 5` on the first); and that `T_ℓE` is not the zero module, since
over it `range (det ρ)` is `{1}` and closed for free.

⚠️ **Two instance traps**, both inherited from `EllipticCurves.TateModule.ImageThree`, which
documents them: neither `Algebra.IsIntegral ℚ AlgClosedQ` nor `IsGalois ℚ AlgClosedQ` is found by
bare instance search, because `AlgebraicClosure`'s instances are registered against
`AlgebraicClosure.instAlgebra ℚ`, which `DivisionRing.toRatAlgebra` outranks. Both are introduced
with `haveI` at the point of use rather than registered.

⚠️ `Fact (Nat.Prime p)` is needed in the *statements* and `private` hides a name, not an instance
(`#1397`); see `EllipticCurves.TateModule.MatrixRepGeneral` for the full note. `by decide`, not
`by norm_num`. -/

section Nonvacuity

open EllipticCurves.Fixture

private instance factPrimeFiveImg : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance factPrimeSevenImg : Fact (Nat.Prime 7) := ⟨by decide⟩

private lemma exampleIsIntegralImg : Algebra.IsIntegral ℚ AlgClosedQ := by
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    rw [show (DivisionRing.toRatAlgebra : Algebra ℚ (AlgebraicClosure ℚ))
        = AlgebraicClosure.instAlgebra ℚ from Subsingleton.elim _ _]
    infer_instance
  infer_instance

private lemma exampleIsGaloisImg : IsGalois ℚ AlgClosedQ := by
  rw [show (DivisionRing.toRatAlgebra : Algebra ℚ (AlgebraicClosure ℚ))
      = AlgebraicClosure.instAlgebra ℚ from Subsingleton.elim _ _]
  infer_instance

private lemma exampleTwoImg : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleFiveImg : ((5 : ℕ) : AlgClosedQ) ≠ 0 := by
  have : ((5 : ℕ) : AlgClosedQ) = 5 := by push_cast; ring
  rw [this]; norm_num

private lemma exampleSevenImg : ((7 : ℕ) : AlgClosedQ) ≠ 0 := by
  have : ((7 : ℕ) : AlgClosedQ) = 7 := by push_cast; ring
  rw [this]; norm_num

open Classical in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on a curve that exists, over a base field `S = ℚ` whose
absolute Galois group is not trivial, the image of `det ρ_{E,5}` really is a closed subset of
`ℤ_[5]ˣ`. `5` is the first prime at which no earlier statement on this front reaches it:
`EllipticCurves.TateModule.Image` is `ℓ = 2` and `…ImageThree` is `ℓ = 3`. The statement is
restated in full rather than obtained-and-projected (`#916`). -/
example : IsClosed (Set.range (galoisDet (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) (ℓ := 5))) := by
  haveI := exampleIsIntegralImg
  haveI := exampleIsGaloisImg
  exact isClosed_range_galoisDet_of_natCast_ne_zero exampleTwoImg exampleFiveImg

open Classical in
/-- ⚠️ **`ℓ = 7`, on a SECOND curve**, and the compactness half rather than the closedness one.
`y² = x³ + 1` (Δ = −432) is not the fixture the `ℓ = 5` block uses. This is the certificate that
the statement is not `{2, 3, 5}`-parametrised. -/
example : IsCompact (Set.range (galoisDet (W' := y2EqX3AddOne ℚ) (F := AlgClosedQ) (ℓ := 7))) := by
  haveI := exampleIsIntegralImg
  haveI := exampleIsGaloisImg
  exact isCompact_range_galoisDet_of_natCast_ne_zero exampleTwoImg exampleSevenImg

open Classical in
/-- **The module the representation acts on is not the zero module**, at `ℓ = 5`, by a route that
never mentions the image: `T₅E` surjects onto `E[5^k]`, which has `25^k` elements. Without this the
image would be `{1}` and closed for free. -/
example : Infinite (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 5) :=
  tateModule.infinite_tateModule_of_card (Fact.out : (5 : ℕ).Prime).one_lt
    (tateModule.proj_surjective_of_two_ne_zero exampleTwoImg)
    (card_torsion_pow_mul_self_of_natCast_ne_zero exampleTwoImg exampleFiveImg)

end Nonvacuity

end WeierstrassCurve.Affine
