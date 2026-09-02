/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.TateModule.FreeGeneral
import EllipticCurves.TateModule.PrimaryMatrixContinuity

/-!
# `ρ_{E,ℓ}` is a CONTINUOUS `GL₂(ℤ_[ℓ])`-valued representation at EVERY prime `ℓ ≠ char F`

`EllipticCurves.TateModule.PrimaryMatrixContinuity` proves continuity of `ρ_{E,ℓ}`, of
`det ρ_{E,ℓ}` and of `tr ρ_{E,ℓ}` in a *given* basis at an arbitrary prime, and states the three
basis-free consequences — `continuous_galoisDet_of_nonempty`, `continuous_galoisTrace_of_nonempty`
and `exists_continuous_galoisRepMatrix_of_nonempty` — in terms of one input:
`Nonempty (T_ℓE ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])`. **This file supplies that input at every prime `ℓ` with
`(ℓ : F) ≠ 0` and contains no argument**; all three proofs are one line, and the input is
`nonempty_tateModuleEquivProd_of_natCast_ne_zero` (`EllipticCurves.TateModule.FreeGeneral`, `#268`).

This is `EllipticCurves.TateModule.MatrixContinuityThree`'s `continuous_galoisDetThree`,
`continuous_galoisTraceThree` and `exists_continuous_galoisRepMatrixThree` with `3` replaced by an
arbitrary prime away from the characteristic, and it is the `MatrixContinuity` entry of `#1533`
item 4's list.

## Why continuity is a constraint and not a formality

`Continuous ρ` into a **discrete** codomain is free. `GL₂(ℤ_[ℓ])` is not discrete — that is
`Matrix.GeneralLinearGroup.not_discreteTopology_padicInt`, stated at an arbitrary prime in
`EllipticCurves.TateModule.PrimaryImageProfinite` — so the statements below say something. The
*Non-vacuity* section cites it at `ℓ = 5` rather than restating it.

⚠️ **Continuous, not locally constant, and the difference is not cosmetic.** `ρ_{E,ℓ}` is
continuous without being locally constant; `ker ρ_{E,ℓ}` is closed and in general not open. That is
the shape the Néron–Ogg–Shafarevich criterion consumes and it is `#73`, which is not this issue.

## What this file does NOT do

* **No `def`s and no `…General` twins.** `galoisDet`, `galoisTrace` and `galoisRepMatrix` already
  are the general-`ℓ` definitions, and every basis-parametrised continuity lemma in
  `PrimaryMatrixContinuity` is already stated at an arbitrary prime. Only the three basis-**free**
  statements had an input to supply.
* **Nothing at `ℓ = char F`**, where `T_ℓE` has rank `0` or `1`.
* `EllipticCurves.TateModule.MatrixContinuityThree` is **not** deleted; it reaches `ℓ = 3` by an
  independent route (`x(3P) = Φ₃/Ψ₃²`) and the `_three` names are consumed downstream.

## Main statements

* `WeierstrassCurve.Affine.continuous_galoisDet_of_natCast_ne_zero`
* `WeierstrassCurve.Affine.continuous_galoisTrace_of_natCast_ne_zero`
* `WeierstrassCurve.Affine.exists_continuous_galoisRepMatrix_of_natCast_ne_zero`

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open Matrix

open scoped WeierstrassCurve.Affine.ProfiniteTopology

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
variable {ℓ : ℕ} [Fact ℓ.Prime]
variable [Algebra.IsIntegral S F] [IsAlgClosed F] [(W'⁄F).IsElliptic]

/-- **`det ρ_{E,ℓ}` is continuous**, at every prime `ℓ` with `(ℓ : F) ≠ 0`, with no basis supplied.

⚠️ **Deletion test**, measured on this file as committed. Replacing the argument
`(tateModule.nonempty_tateModuleEquivProd_of_natCast_ne_zero h2 hl)` by a hole — `by refine
continuous_galoisDet_of_nonempty (W' := W') (F := F) (ℓ := ℓ) ?_` — leaves

```
error: unsolved goals
S : Type u_1
F : Type u_2
inst✝⁷ : Field S
inst✝⁶ : Field F
inst✝⁵ : DecidableEq F
inst✝⁴ : Algebra S F
W' : Affine S
ℓ : ℕ
inst✝³ : Fact (Nat.Prime ℓ)
inst✝² : Algebra.IsIntegral S F
inst✝¹ : IsAlgClosed F
inst✝ : WeierstrassCurve.IsElliptic W'⁄F
h2 : 2 ≠ 0
hl : ↑ℓ ≠ 0
⊢ Nonempty (↥((W'⁄F).tateModule ℓ) ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])
```

⚠️ `h2` and `hl` both **survive**, so the deletion removes a construction and not a hypothesis, and
the residual is a **goal** rather than a type mismatch. -/
theorem continuous_galoisDet_of_natCast_ne_zero (h2 : (2 : F) ≠ 0) (hl : (ℓ : F) ≠ 0) :
    Continuous (galoisDet (W' := W') (F := F) (ℓ := ℓ)) :=
  continuous_galoisDet_of_nonempty
    (tateModule.nonempty_tateModuleEquivProd_of_natCast_ne_zero h2 hl)

/-- **`tr ρ_{E,ℓ}` is continuous**, at every prime `ℓ` with `(ℓ : F) ≠ 0`, with no basis
supplied. -/
theorem continuous_galoisTrace_of_natCast_ne_zero (h2 : (2 : F) ≠ 0) (hl : (ℓ : F) ≠ 0) :
    Continuous (galoisTrace (W' := W') (F := F) (ℓ := ℓ)) :=
  continuous_galoisTrace_of_nonempty
    (tateModule.nonempty_tateModuleEquivProd_of_natCast_ne_zero h2 hl)

/-- **`ρ_{E,ℓ}` is a continuous `ℓ`-adic matrix representation, at every prime `ℓ` with
`(ℓ : F) ≠ 0`**: there are a basis of `T_ℓE` and a *continuous* homomorphism
`ρ : G →* GL₂(ℤ_[ℓ])` whose matrices act on coordinate vectors the way `G` acts on `T_ℓE`.

⚠️ The compatibility clause is what stops this from being vacuous: `Continuous ρ` on its own is
witnessed by the trivial homomorphism and would not mention the curve. -/
theorem exists_continuous_galoisRepMatrix_of_natCast_ne_zero (h2 : (2 : F) ≠ 0)
    (hl : (ℓ : F) ≠ 0) :
    ∃ (b : Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ))
      (ρ : (F ≃ₐ[S] F) →* GL (Fin 2) ℤ_[ℓ]), Continuous ρ ∧
        ∀ (σ : F ≃ₐ[S] F) (f : (W'⁄F).tateModule ℓ),
          ⇑(b.repr (σ • f)) = (ρ σ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) *ᵥ ⇑(b.repr f) :=
  exists_continuous_galoisRepMatrix_of_nonempty
    (tateModule.nonempty_tateModuleEquivProd_of_natCast_ne_zero h2 hl)

/-! ### Non-vacuity

Four risks, four certificates, following
`EllipticCurves.TateModule.MatrixContinuityThree`'s block and
`EllipticCurves.TateModule.MatrixRepGeneral`'s generality requirement.

⚠️ **The `ℚ`-algebra instance trap** applies here as it does at `ℓ = 3`:
`Algebra.IsIntegral ℚ AlgClosedQ` is not found by bare instance search, because
`DivisionRing.toRatAlgebra` outranks `AlgebraicClosure.instAlgebra ℚ` once `ℤ_[ℓ]` has pulled in
the analysis imports. It is supplied as a `private lemma` and introduced with `haveI` at the point
of use, so no importing file silently acquires a `ℚ`-specific instance.

⚠️ `Fact (Nat.Prime p)` is needed in the *statements*, and `private` hides a name, not an instance
(`#1397`); see `EllipticCurves.TateModule.MatrixRepGeneral` for the full note. `by decide`, not
`by norm_num`. -/

section Nonvacuity

open EllipticCurves.Fixture

private instance factPrimeFiveCont : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance factPrimeSevenCont : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- **⚠️ THE CERTIFICATE THAT THE STATEMENTS ARE NOT FREE**: `GL₂(ℤ_[5])` is not discrete, so
continuity into it is a constraint on `ρ_{E,5}` rather than a formality. ⚠️ A **citation** and not
a restatement — the theorem is at an arbitrary prime already. -/
example : ¬ DiscreteTopology (GL (Fin 2) ℤ_[5]) :=
  Matrix.GeneralLinearGroup.not_discreteTopology_padicInt 5

private lemma exampleIsIntegralCont : Algebra.IsIntegral ℚ AlgClosedQ := by
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    rw [show (DivisionRing.toRatAlgebra : Algebra ℚ (AlgebraicClosure ℚ))
        = AlgebraicClosure.instAlgebra ℚ from Subsingleton.elim _ _]
    infer_instance
  infer_instance

private lemma exampleTwoCont : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleFiveCont : ((5 : ℕ) : AlgClosedQ) ≠ 0 := by
  have : ((5 : ℕ) : AlgClosedQ) = 5 := by push_cast; ring
  rw [this]; norm_num

private lemma exampleSevenCont : ((7 : ℕ) : AlgClosedQ) ≠ 0 := by
  have : ((7 : ℕ) : AlgClosedQ) = 7 := by push_cast; ring
  rw [this]; norm_num

open Classical in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on a curve that exists, over a base field `S = ℚ` whose
absolute Galois group is not trivial, `ρ_{E,5}` really is a **continuous** `GL₂(ℤ_[5])`-valued
representation computing the Galois action. `5` is the first prime at which no earlier statement on
this front does so. Restated in full rather than obtained-and-projected (`#916`), compatibility
clause kept. -/
example : ∃ (b : Module.Basis (Fin 2) ℤ_[5] (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 5))
    (ρ : (AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) →* GL (Fin 2) ℤ_[5]), Continuous ρ ∧
      ∀ (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ)
        (f : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 5),
        ⇑(b.repr (σ • f)) = (ρ σ : Matrix (Fin 2) (Fin 2) ℤ_[5]) *ᵥ ⇑(b.repr f) := by
  haveI := exampleIsIntegralCont
  exact exists_continuous_galoisRepMatrix_of_natCast_ne_zero exampleTwoCont exampleFiveCont

open Classical in
/-- ⚠️ **`ℓ = 7`, on a SECOND curve** `y² = x³ + 1` (Δ = −432), and the determinant and trace halves
rather than the representation. This is the certificate that the statements are not
`{2, 3, 5}`-parametrised, which `ℓ = 5` alone cannot give. -/
example : Continuous (galoisDet (W' := y2EqX3AddOne ℚ) (F := AlgClosedQ) (ℓ := 7)) ∧
    Continuous (galoisTrace (W' := y2EqX3AddOne ℚ) (F := AlgClosedQ) (ℓ := 7)) := by
  haveI := exampleIsIntegralCont
  exact ⟨continuous_galoisDet_of_natCast_ne_zero exampleTwoCont exampleSevenCont,
    continuous_galoisTrace_of_natCast_ne_zero exampleTwoCont exampleSevenCont⟩

open Classical in
/-- **The module the matrices act on is not the zero module**, at `ℓ = 5`, by a route that never
mentions the representation or continuity: `T₅E` surjects onto `E[5^k]`, which has `25^k`
elements. -/
example : Infinite (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 5) :=
  tateModule.infinite_tateModule_of_card (Fact.out : (5 : ℕ).Prime).one_lt
    (tateModule.proj_surjective_of_two_ne_zero exampleTwoCont)
    (card_torsion_pow_mul_self_of_natCast_ne_zero exampleTwoCont exampleFiveCont)

end Nonvacuity

end WeierstrassCurve.Affine
