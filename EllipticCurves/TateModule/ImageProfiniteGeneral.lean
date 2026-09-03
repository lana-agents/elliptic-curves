/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.TateModule.FreeGeneral
import EllipticCurves.TateModule.PrimaryImageProfinite

/-!
# The image of `det ρ_{E,ℓ}` as a closed subgroup and a profinite group, at EVERY prime `ℓ ≠ char F`

`EllipticCurves.TateModule.PrimaryImageProfinite` bundles `range (det ρ_{E,ℓ})` as a
`ClosedSubgroup ℤ_[ℓ]ˣ` and as a `ProfiniteGrp` at an arbitrary prime, and states the three
basis-free forms in terms of one input: `Nonempty (T_ℓE ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])`. **This file
supplies that input at every prime `ℓ` with `(2 : F) ≠ 0` and `(ℓ : F) ≠ 0`, and contains no
argument**; all three proofs are one line, and the input is
`nonempty_tateModuleEquivProd_of_natCast_ne_zero` (`EllipticCurves.TateModule.FreeGeneral`,
`#268`). ⚠️ **`(2 : F) ≠ 0` is the second hypothesis, and this paragraph used to name only the
first** — see `EllipticCurves.Torsion.StructureGeneral`, where it enters, for why it is there and
why it is not the same kind of restriction as `(ℓ : F) ≠ 0`.

This is `EllipticCurves.TateModule.ImageProfiniteThree`'s primed trio
(`closedSubgroupRangeGaloisDetThree'`, `profiniteGrpRangeGaloisDetThree'`,
`coe_profiniteGrpRangeGaloisDetThree'`) with `3` replaced by an arbitrary prime away from the
characteristic, and it is the `ImageProfinite` entry of `#1533` item 4's list.

## ⚠️ Why this file DOES declare `def`s, when `MatrixRepGeneral` and `DeterminantGeneral` do not

The settled rule on this front is that a `…General` twin of an *already-generic* definition is pure
duplication — `EllipticCurves.TateModule.MatrixRepGeneral` declines to twin `tateModuleBasis`,
`matrixAutEquiv` and `galoisRepMatrix` for exactly that reason, and this file declines to twin
`closedSubgroupRangeGaloisRepMatrix`, `profiniteGrpRangeGaloisRepMatrix`,
`continuousGaloisRepMatrix` or `profiniteGrpHomGaloisRepMatrix`, all of which take a basis and are
already stated at an arbitrary prime.

The two `def`s below are **not** that case. `closedSubgroupRangeGaloisDet_of_nonempty` and
`profiniteGrpRangeGaloisDet_of_nonempty` are `Data`, not `Prop`, and they take the rank-two input as
an *explicit argument*: their values depend on which proof of `Nonempty …` is supplied only up to
proof-irrelevance of the underlying subgroup, but their **types** cannot be written down without
supplying one. So the basis-free spelling at a general prime is a genuinely new name, exactly as
`…Three'` is at `ℓ = 3`, and it is the spelling a consumer with `h2` and `hl` in hand can use.
⚠️ That is the only scope judgement in this file; a reviewer who wants to disagree should disagree
with it.

## What this file does NOT do

* **Not surjectivity, not openness of the image, not Serre.** *"`range (det ρ_{E,ℓ})` is profinite"*
  says nothing about *which* subgroup of `ℤ_[ℓ]ˣ` it is; openness of the image is a different
  theorem and nothing here supplies it.
* **Not `det ρ_{E,ℓ} = χ_ℓ`.**
* **Nothing at `ℓ = char F`**, where `T_ℓE` has rank `0` or `1` and the input does not exist.
* `EllipticCurves.TateModule.ImageProfiniteThree` is **not** deleted; it reaches `ℓ = 3` by an
  independent route and the `_three` names are consumed downstream.

## Main definitions

* `WeierstrassCurve.Affine.closedSubgroupRangeGaloisDet_of_natCast_ne_zero` :
  `range (det ρ_{E,ℓ})` as a `ClosedSubgroup ℤ_[ℓ]ˣ`.
* `WeierstrassCurve.Affine.profiniteGrpRangeGaloisDet_of_natCast_ne_zero` : the same as a
  `ProfiniteGrp`.

## Main statements

* `WeierstrassCurve.Affine.coe_profiniteGrpRangeGaloisDet_of_natCast_ne_zero` : its carrier is
  `range (det ρ_{E,ℓ})`, so the bundling is of the intended object.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open Matrix Topology

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
variable {ℓ : ℕ} [Fact ℓ.Prime]
variable [Algebra.IsIntegral S F] [IsGalois S F] [IsAlgClosed F] [(W'⁄F).IsElliptic]

/-- **The image of `det ρ_{E,ℓ}` as a closed subgroup of `ℤ_[ℓ]ˣ`**, at every prime `ℓ` with
`(2 : F) ≠ 0` and `(ℓ : F) ≠ 0`, with no basis supplied.

⚠️ **Deletion test**, measured on this file as committed. Replacing the argument
`(tateModule.nonempty_tateModuleEquivProd_of_natCast_ne_zero h2 hl)` by a hole — `by refine
closedSubgroupRangeGaloisDet_of_nonempty (W' := W') (F := F) (ℓ := ℓ) ?_` — leaves

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
hypothesis, and the residual is a **goal**. It is `#268`'s theorem.

⚠️ `nolint defsWithUnderscore` (`#1277`): `_of_natCast_ne_zero` names the hypothesis, exactly as the
`_of_basis` and `_of_nonempty` definitions this is built from do
(`EllipticCurves.TateModule.PrimaryImageProfinite`), and as `#592`'s and `#594`'s theorems do. The
two definitions in this file are one naming decision, not two. -/
@[nolint defsWithUnderscore]
noncomputable def closedSubgroupRangeGaloisDet_of_natCast_ne_zero (h2 : (2 : F) ≠ 0)
    (hl : (ℓ : F) ≠ 0) : ClosedSubgroup ℤ_[ℓ]ˣ :=
  closedSubgroupRangeGaloisDet_of_nonempty (W' := W')
    (tateModule.nonempty_tateModuleEquivProd_of_natCast_ne_zero h2 hl)

/-- **The image of `det ρ_{E,ℓ}` is a profinite group**, at every prime `ℓ` with `(2 : F) ≠ 0` and
`(ℓ : F) ≠ 0`, basis-free form.

⚠️ `nolint defsWithUnderscore` (`#1277`) — see `closedSubgroupRangeGaloisDet_of_natCast_ne_zero`. -/
@[nolint defsWithUnderscore]
noncomputable def profiniteGrpRangeGaloisDet_of_natCast_ne_zero (h2 : (2 : F) ≠ 0)
    (hl : (ℓ : F) ≠ 0) : ProfiniteGrp :=
  profiniteGrpRangeGaloisDet_of_nonempty (W' := W')
    (tateModule.nonempty_tateModuleEquivProd_of_natCast_ne_zero h2 hl)

/-- The carrier of `profiniteGrpRangeGaloisDet_of_natCast_ne_zero` is the image of `det ρ_{E,ℓ}`.

⚠️ This is what stops the two definitions above from being bundles of *something else*: a
`ProfiniteGrp` with no identification of its carrier would be certified by the trivial group. -/
theorem coe_profiniteGrpRangeGaloisDet_of_natCast_ne_zero (h2 : (2 : F) ≠ 0) (hl : (ℓ : F) ≠ 0) :
    (profiniteGrpRangeGaloisDet_of_natCast_ne_zero (W' := W') (F := F) (ℓ := ℓ) h2 hl : Type _)
      = (galoisDet (W' := W') (F := F) (ℓ := ℓ)).range :=
  coe_profiniteGrpRangeGaloisDet_of_nonempty (W' := W')
    (tateModule.nonempty_tateModuleEquivProd_of_natCast_ne_zero h2 hl)

/-! ### Non-vacuity

⚠️ A `ProfiniteGrp` is `Data`, so *"it exists"* is not the risk — the risks are that its carrier is
the wrong object, that the hypotheses are unsatisfiable, and that the whole thing is the trivial
group. Three certificates, plus the generality one that
`EllipticCurves.TateModule.MatrixRepGeneral` requires: `ℓ = 5` on the standard fixture and `ℓ = 7`
on a **second** curve, since `ℓ = 5` alone proves only that `{2, 3}` was left.

⚠️ **Two instance traps**, both inherited from `EllipticCurves.TateModule.ImageThree`: neither
`Algebra.IsIntegral ℚ AlgClosedQ` nor `IsGalois ℚ AlgClosedQ` is found by bare instance search,
because `AlgebraicClosure`'s instances are registered against `AlgebraicClosure.instAlgebra ℚ`,
which `DivisionRing.toRatAlgebra` outranks. Both are `private lemma`s introduced with `haveI`.

⚠️ `Fact (Nat.Prime p)` is needed in the *statements*, and `private` hides a name, not an instance
(`#1397`); see `EllipticCurves.TateModule.MatrixRepGeneral`. `by decide`, not `by norm_num`. -/

section Nonvacuity

open EllipticCurves.Fixture

private instance factPrimeFiveProf : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance factPrimeSevenProf : Fact (Nat.Prime 7) := ⟨by decide⟩

private lemma exampleIsIntegralProf : Algebra.IsIntegral ℚ AlgClosedQ := by
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    rw [show (DivisionRing.toRatAlgebra : Algebra ℚ (AlgebraicClosure ℚ))
        = AlgebraicClosure.instAlgebra ℚ from Subsingleton.elim _ _]
    infer_instance
  infer_instance

private lemma exampleIsGaloisProf : IsGalois ℚ AlgClosedQ := by
  rw [show (DivisionRing.toRatAlgebra : Algebra ℚ (AlgebraicClosure ℚ))
      = AlgebraicClosure.instAlgebra ℚ from Subsingleton.elim _ _]
  infer_instance

private lemma exampleTwoProf : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleFiveProf : ((5 : ℕ) : AlgClosedQ) ≠ 0 := by
  have : ((5 : ℕ) : AlgClosedQ) = 5 := by push_cast; ring
  rw [this]; norm_num

private lemma exampleSevenProf : ((7 : ℕ) : AlgClosedQ) ≠ 0 := by
  have : ((7 : ℕ) : AlgClosedQ) = 7 := by push_cast; ring
  rw [this]; norm_num

open Classical in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on a curve that exists, over a base field `S = ℚ` whose
absolute Galois group is not trivial, there really is a profinite group whose carrier is the image
of `det ρ_{E,5}`. `5` is the first prime at which no earlier statement on this front produces one:
`EllipticCurves.TateModule.ImageProfinite` is `ℓ = 2` and `…ImageProfiniteThree` is `ℓ = 3`.

⚠️ The bundle is **existentially quantified inside the statement** rather than named in it, so the
certificate does not depend on the elaborator finding the two `ℚ`-instance traps in the statement's
own type; and it closes by **application** of the `coe` theorem rather than by `rfl`, `decide` or
`norm_num`, so it consumes both declarations it certifies. Without the carrier clause the trivial
group would witness it. -/
example : ∃ G : ProfiniteGrp,
    (G : Type _) = (galoisDet (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) (ℓ := 5)).range := by
  haveI := exampleIsIntegralProf
  haveI := exampleIsGaloisProf
  exact ⟨profiniteGrpRangeGaloisDet_of_natCast_ne_zero exampleTwoProf exampleFiveProf,
    coe_profiniteGrpRangeGaloisDet_of_natCast_ne_zero exampleTwoProf exampleFiveProf⟩

open Classical in
/-- ⚠️ **`ℓ = 7`, on a SECOND curve** `y² = x³ + 1` (Δ = −432), and the `ClosedSubgroup` bundle
rather than the `ProfiniteGrp` one. This is the certificate that the file is not
`{2, 3, 5}`-parametrised, which `ℓ = 5` alone cannot give. -/
example : ∃ K : ClosedSubgroup ℤ_[7]ˣ,
    K.toSubgroup = (galoisDet (W' := y2EqX3AddOne ℚ) (F := AlgClosedQ) (ℓ := 7)).range := by
  haveI := exampleIsIntegralProf
  haveI := exampleIsGaloisProf
  exact ⟨closedSubgroupRangeGaloisDet_of_natCast_ne_zero exampleTwoProf exampleSevenProf, rfl⟩

open Classical in
/-- **The module the determinant is taken on is not the zero module**, at `ℓ = 5`, by a route that
never mentions profiniteness or the determinant: `T₅E` surjects onto `E[5^k]`, which has `25^k`
elements. Without this the image would be the trivial group and profinite for free. -/
example : Infinite (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 5) :=
  tateModule.infinite_tateModule_of_card (Fact.out : (5 : ℕ).Prime).one_lt
    (tateModule.proj_surjective_of_two_ne_zero exampleTwoProf)
    (card_torsion_pow_mul_self_of_natCast_ne_zero exampleTwoProf exampleFiveProf)

end Nonvacuity

end WeierstrassCurve.Affine
