/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.TateModule.FreeGeneral
import EllipticCurves.TateModule.Kernel
import EllipticCurves.TateModule.OpenKernel

/-!
# `ker ρ_{E,ℓ}` is closed at EVERY prime `ℓ ≠ char F`

`EllipticCurves.TateModule.OpenKernel` proves `IsClosed (ker ρ_{E,ℓ})` at `ℓ = 2`
(`isClosed_ker_galoisRepTwo`) and at `ℓ = 3` (`isClosed_ker_galoisRepThree`), by writing the kernel
as `⨅ k, ker (galoisRepMod (ℓ^k))` — a countable intersection of open, hence closed, subgroups.
**This file states it at every prime `ℓ` with `(ℓ : F) ≠ 0`**, and adds the matrix-layer corollary
that `EllipticCurves.TateModule.MatrixRepBasisChangeThree` states at `ℓ = 3`.

⚠️ **This is the one file in `#1533`'s package that is NOT a pure instantiation, and saying so is
the point.** The other five general leaves — `MatrixRepGeneral`, `DeterminantGeneral`,
`ImageGeneral`, `MatrixContinuityGeneral`, `ImageProfiniteGeneral` — each supply
`Nonempty (T_ℓE ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])` to a generic sibling that already takes it as an argument,
and their proofs are one line. There is **no** `isClosed_ker_galoisRep_of_nonempty` to instantiate:
`isClosed_ker_galoisRepThree`'s proof is written at `ℓ = 3` and its two inputs are

* the level filtration `ker_galoisRep_eq_iInf` (`EllipticCurves.TateModule.Kernel`), which is
  **already** general and asks only for surjectivity of `[ℓ]`, supplied by
  `nsmul_surjective_of_two_ne_zero` at every nonzero index; and
* openness of each level kernel, which asks for `Finite (E[ℓ^k])`, supplied by
  `finite_torsion_of_intCast_ne_zero` (`EllipticCurves.Torsion.XSupport`) at every `n` with
  `(n : F) ≠ 0`.

So the general proof is four lines rather than one, and both of its inputs were already on `main`
before `#268`. ⚠️ **In particular this file does not consume `#268` at all** — it needs finiteness
of `E[ℓ^k]`, not the rank-two structure — and it is the one place on this front where *"the generic
layer needs no change"* was not quite true. It is recorded here rather than left as a sixth file
nobody files.

## What this file does NOT do

* **It does not claim `ker ρ_{E,ℓ}` is OPEN, and in general it is not.** `ρ_{E,ℓ}` is continuous
  without being locally constant; each *level* kernel `ker (galoisRepMod (ℓ^k))` is open, and their
  intersection over all `k` need not be. That asymmetry is `isClosed_ker_galoisRepTwo`'s docstring
  and it is insensitive to `ℓ`.
* **It is not `#73`.** *"Closed kernel"* is the shape the Néron–Ogg–Shafarevich criterion consumes,
  not the criterion; that needs a Galois action over a non-closed base with an inertia subgroup,
  and every statement here assumes `[IsAlgClosed F]`.
* **Nothing at `ℓ = char F`**, where `E[ℓ^k]` is not `(ℤ/ℓ^kℤ)²` and `(ℓ : F) ≠ 0` fails at the
  first step.
* `isClosed_ker_galoisRepTwo` and `isClosed_ker_galoisRepThree` are **not** deleted: they are the
  `ℓ = 2` and `ℓ = 3` statements in the spellings their consumers use, and at `ℓ = 2`
  `isClosed_ker_galoisRepTwo` carries only `h2` where the general statement would ask for `h2` and
  `(2 : F) ≠ 0` separately.

## Main statements

* `WeierstrassCurve.Affine.isClosed_ker_galoisRep_of_natCast_ne_zero` : `ker ρ_{E,ℓ}` is closed.
* `WeierstrassCurve.Affine.isClosed_ker_galoisRepMatrix_of_natCast_ne_zero` : the same for the
  matrix representation in any basis — the general form of
  `isClosed_ker_galoisRepMatrixThree`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7 and VII.7.
-/

open Matrix

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
variable {ℓ : ℕ} [Fact ℓ.Prime]
variable [Algebra.IsIntegral S F] [IsAlgClosed F] [(W'⁄F).IsElliptic]

/-- **`ker ρ_{E,ℓ}` is closed, at every prime `ℓ` with `(ℓ : F) ≠ 0`.** By `ker_galoisRep_eq_iInf`
(`EllipticCurves.TateModule.Kernel`) it is `⨅ k, ker (galoisRepMod (ℓ^k))`, a countable
intersection of open — hence also closed — subgroups.

⚠️ **`h2` and `hl` enter through different doors**, exactly as at `ℓ = 3`. `h2` gives the level
filtration, because `nsmul_surjective_of_two_ne_zero` needs nothing more than `ℓ ≠ 0` beyond it;
`hl` is what `finite_torsion_of_intCast_ne_zero` needs to make each level kernel *open*. The
`ℓ = 2` statement `isClosed_ker_galoisRepTwo` carries only `h2` because at `ℓ = 2` both doors open
with it.

⚠️ It is **not** claimed open, and in general it is not — see `isClosed_ker_galoisRepTwo` for the
reason, which is insensitive to `ℓ`.

⚠️ **Deletion test**, measured on this file as committed. Replacing the last line's argument by a
hole — `refine finite_torsion_of_intCast_ne_zero h2 (n := ℓ ^ k) ?_` — leaves

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
k : ℕ
⊢ ↑(ℓ ^ k) ≠ 0
```

⚠️ `h2` and `hl` both **survive**, and the residual is a **goal** rather than a type mismatch. Note
that it is `↑(ℓ ^ k) ≠ 0` and not `↑ℓ ≠ 0`: what `hl` buys here is invertibility of every *power*
of `ℓ`, which is what makes each `E[ℓ^k]` finite and hence each level kernel open. ⚠️ Unlike the
other five general leaves on this front, the residual is **not** `#268`'s rank-two input — this
file does not consume `#268`. -/
theorem isClosed_ker_galoisRep_of_natCast_ne_zero (h2 : (2 : F) ≠ 0) (hl : (ℓ : F) ≠ 0) :
    IsClosed ((galoisRep (W' := W') (F := F) ℓ).ker : Set (F ≃ₐ[S] F)) := by
  rw [ker_galoisRep_eq_iInf ℓ
      (nsmul_surjective_of_two_ne_zero h2 (Fact.out : ℓ.Prime).pos.ne'), Subgroup.coe_iInf]
  refine isClosed_iInter fun k => OpenSubgroup.isClosed (openSubgroupKerGaloisRepMod (ℓ ^ k) ?_)
  exact finite_torsion_of_intCast_ne_zero h2 (by push_cast; exact pow_ne_zero _ hl)

/-- **`ker ρ_{E,ℓ}` is closed in matrix form too**, in any basis of `T_ℓE`, at every prime `ℓ` with
`(ℓ : F) ≠ 0`. This is the general form of `isClosed_ker_galoisRepMatrixThree`
(`EllipticCurves.TateModule.MatrixRepBasisChangeThree`).

⚠️ The basis does not matter and the proof says so: `ker_galoisRepMatrix`
(`EllipticCurves.TateModule.Kernel`) identifies `ker (ρ_b)` with `ker ρ_{E,ℓ}` for *every* `b`,
because passing to matrices is an isomorphism onto `Aut_{ℤ_[ℓ]}(T_ℓE)`. Nothing here is a statement
about coordinates. -/
theorem isClosed_ker_galoisRepMatrix_of_natCast_ne_zero
    (b : Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ)) (h2 : (2 : F) ≠ 0) (hl : (ℓ : F) ≠ 0) :
    IsClosed ((galoisRepMatrix b).ker : Set (F ≃ₐ[S] F)) := by
  rw [ker_galoisRepMatrix b]
  exact isClosed_ker_galoisRep_of_natCast_ne_zero h2 hl

/-! ### Non-vacuity

⚠️ *"A subgroup is closed"* is **free over the zero module** — there `ker ρ` is everything, and
everything is closed. So the `Infinite` certificate is not decoration here; it is what makes the
statement about a representation rather than about a point. Four certificates: the hypotheses are
satisfiable on a curve that exists over `S = ℚ`; `ℓ = 5`; `ℓ = 7` on a **second** curve, since
`ℓ = 5` alone proves only that `{2, 3}` was left; and `T₅E` is infinite by a route that never
mentions the kernel.

⚠️ **The `ℚ`-algebra instance trap** applies, as everywhere on this front that carries
`[Algebra.IsIntegral S F]`: it is supplied as a `private lemma` and introduced with `haveI` at the
point of use rather than registered.

⚠️ `Fact (Nat.Prime p)` is needed in the *statements*, and `private` hides a name, not an instance
(`#1397`); see `EllipticCurves.TateModule.MatrixRepGeneral`. `by decide`, not `by norm_num`. -/

section Nonvacuity

open EllipticCurves.Fixture

private instance factPrimeFiveKer : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance factPrimeSevenKer : Fact (Nat.Prime 7) := ⟨by decide⟩

private lemma exampleIsIntegralKer : Algebra.IsIntegral ℚ AlgClosedQ := by
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    rw [show (DivisionRing.toRatAlgebra : Algebra ℚ (AlgebraicClosure ℚ))
        = AlgebraicClosure.instAlgebra ℚ from Subsingleton.elim _ _]
    infer_instance
  infer_instance

private lemma exampleTwoKer : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleFiveKer : ((5 : ℕ) : AlgClosedQ) ≠ 0 := by
  have : ((5 : ℕ) : AlgClosedQ) = 5 := by push_cast; ring
  rw [this]; norm_num

private lemma exampleSevenKer : ((7 : ℕ) : AlgClosedQ) ≠ 0 := by
  have : ((7 : ℕ) : AlgClosedQ) = 7 := by push_cast; ring
  rw [this]; norm_num

open Classical in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on a curve that exists, over a base field `S = ℚ` whose
absolute Galois group is not trivial, `ker ρ_{E,5}` really is closed. `5` is the first prime at
which no earlier statement in this development says so: `isClosed_ker_galoisRepTwo` is `ℓ = 2` and
`isClosed_ker_galoisRepThree` is `ℓ = 3`. Restated in full rather than obtained-and-projected
(`#916`). -/
example : IsClosed ((galoisRep (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) 5).ker :
    Set (AlgClosedQ ≃ₐ[ℚ] AlgClosedQ)) := by
  haveI := exampleIsIntegralKer
  exact isClosed_ker_galoisRep_of_natCast_ne_zero exampleTwoKer exampleFiveKer

open Classical in
/-- ⚠️ **`ℓ = 7`, on a SECOND curve** `y² = x³ + 1` (Δ = −432), and the **matrix** form rather than
the bare one, with the basis existentially quantified so that the certificate does not assume a
family that might be empty. This is what shows the file is not `{2, 3, 5}`-parametrised. -/
example : ∃ b : Module.Basis (Fin 2) ℤ_[7] (((y2EqX3AddOne ℚ)⁄AlgClosedQ).tateModule 7),
    IsClosed ((galoisRepMatrix (S := ℚ) b).ker : Set (AlgClosedQ ≃ₐ[ℚ] AlgClosedQ)) := by
  haveI := exampleIsIntegralKer
  obtain ⟨b⟩ := tateModule.nonempty_basis_tateModule_of_nonempty
    (tateModule.nonempty_tateModuleEquivProd_of_natCast_ne_zero
      (W := (y2EqX3AddOne ℚ)⁄AlgClosedQ) exampleTwoKer exampleSevenKer)
  exact ⟨b, isClosed_ker_galoisRepMatrix_of_natCast_ne_zero b exampleTwoKer exampleSevenKer⟩

open Classical in
/-- **The module the kernel is a kernel of an action on is not the zero module**, at `ℓ = 5`, by a
route that never mentions the kernel: `T₅E` surjects onto `E[5^k]`, which has `25^k` elements.
⚠️ Without this the statement above would be *"the whole group is closed"*. -/
example : Infinite (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 5) :=
  tateModule.infinite_tateModule_of_card (Fact.out : (5 : ℕ).Prime).one_lt
    (tateModule.proj_surjective_of_two_ne_zero exampleTwoKer)
    (card_torsion_pow_mul_self_of_natCast_ne_zero exampleTwoKer exampleFiveKer)

end Nonvacuity

end WeierstrassCurve.Affine
