/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.TateModule.FreeGeneral
import EllipticCurves.TateModule.PrimaryMatrixRep

/-!
# `ρ_{E,ℓ} : G → GL₂(ℤ_ℓ)` at EVERY prime `ℓ ≠ char F`

For a Weierstrass curve `W'` over a field `S`, an algebraically closed extension `F / S` with
`(2 : F) ≠ 0` for which `W'⁄F` is elliptic, and `G = F ≃ₐ[S] F`, the `ℓ`-adic Galois representation
is a representation by invertible `2 × 2` matrices over `ℤ_[ℓ]`:

```
∃ b ρ, ∀ σ f, b.repr (σ • f) = ρ σ *ᵥ b.repr f
```

at **every** prime `ℓ` with `(ℓ : F) ≠ 0`, with no restriction to `ℓ ∈ {2, 3}` and no parity
condition.

## What this file contains, and what it does not

The transport is in `EllipticCurves.TateModule.PrimaryMatrixRep`, stated for an arbitrary prime `ℓ`
in terms of one input: `Nonempty (T_ℓE ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])`. **This file supplies that input
at every prime `ℓ` with `(ℓ : F) ≠ 0` and contains no argument.** The input is
`nonempty_tateModuleEquivProd_of_natCast_ne_zero` (`EllipticCurves.TateModule.FreeGeneral`,
`#268`), and both proofs below are one line.

⚠️ **This is the general-`ℓ` mirror of `EllipticCurves.TateModule.MatrixRepThree`, and its two
theorems are that file's two theorems with `_three` replaced by `_of_natCast_ne_zero`.** Nothing is
invented, and in particular no Galois theory is done here; what is new is that the rank-two input
exists at every prime.

Census: **2 public theorems, 7 private declarations** (three `Fact (Nat.Prime p)` instances and
four field certificates, all in the *Non-vacuity* block) **and 4 `example`s**. There are **no
`def`s** — see the next section for why that is deliberate.

⚠️ `(ℓ : F) ≠ 0` is **sharp**, not a relaxed smoothness or a relaxed parity: at `ℓ = char F` the
conclusion is *false*, not unproved. There `E[ℓ]` is `0` or `ℤ/ℓℤ`, never `(ℤ/ℓℤ)²`, so `T_ℓE` has
rank `0` or `1` and no `GL₂(ℤ_[ℓ])`-valued representation computes the Galois action on it.

## ⚠️ Why there are no `def`s here, unlike in `MatrixRepThree`

`EllipticCurves.TateModule.MatrixRepThree` declares `tateModuleBasisThree`, `matrixAutEquivThree`
and `galoisRepMatrixThree`, and its *Naming* section explains that those three are a **deliberate
exception** to the settled rule that a twin of an already-generic definition is pure duplication:
their `ℓ = 2` twins predate the extraction and are consumed 100+ times, so leaving `ℓ = 3` without
the matching spellings would put the two primes on different footings.

That reason does not apply here. `tateModuleBasis`, `matrixAutEquiv` and `galoisRepMatrix`
(`EllipticCurves.TateModule.PrimaryMatrixRep`) **are** the general-`ℓ` definitions already, and
every lemma about them — `galoisRepMatrix_mulVec`, `galoisRepMatrix_apply_coe`,
`galoisRepMatrix_smul_basis_eq_sum`, `matrixAutEquiv_galoisRepMatrix` — is already stated at an
arbitrary prime and needs nothing from this file. So a `…General` twin would be duplication with no
compensating reason, and this file declares **two theorems and nothing else**.

## What is *not* here

* **Not the other five `*Three` files.** `EllipticCurves.TateModule.DeterminantThree`,
  `…ImageProfiniteThree`, `…ImageThree`, `…MatrixContinuityThree` and
  `…MatrixRepBasisChangeThree` are the `ℓ = 3` instantiations of `PrimaryDeterminant`,
  `PrimaryImageProfinite`, `PrimaryImage`, `PrimaryMatrixContinuity` and
  `PrimaryMatrixRepBasisChange`, and each is now instantiable at every prime with `(ℓ : F) ≠ 0` by
  exactly the substitution made here. ⚠️ **None of them is touched by this file**, and each is a
  separate PR — `#1533` scope item 2 asks for one file done properly before six.
* **The six gate paragraphs are NOT rewritten here.** Each of those six files carries a *"General
  odd `ℓ ≥ 5` stays out … `#E[5^k]` is genuinely open; its gate list is
  `EllipticCurves.Torsion.PrimaryTower`'s"* bullet, and both of those clauses are false as of
  `#293` / `#268`. ⚠️ They are left alone **deliberately**: PR #590 (`#1522`) rewrites those same
  six paragraphs and is approved and enqueued, so editing them here would be racing an in-flight PR
  through six shared files for no mathematical gain. `#1533` item 4 asks for them, and they are
  what this file still owes.

  ⚠️ **Two things about that text will still be owed after PR #590 lands, and they are different
  from what is owed before it.** #590 replaces the bullet with *"`#E[5^k]` is no longer open at
  `ℓ ≥ 5` … `card_torsion_pow_mul_self_of_odd` supplies it at every **odd** `ℓ` … Instantiating
  this file at `ℓ ≥ 5` on top of that count is separate work and is not done here."* After this
  file, (i) the odd-`ℓ` attribution is true but no longer sharpest — `card_torsion_eq_sq`
  (`EllipticCurves.Torsion.StructureGeneral`, `#293`) is the count at every `n` with
  `(n : F) ≠ 0`, `ℓ = 2` included — and (ii) *"is separate work and is not done here"* should point
  at this module rather than reading as undone. ⚠️ The honest replacement is *"at every prime `ℓ`
  with `(ℓ : F) ≠ 0`"* — **not** *"at every odd `ℓ`"* (`ℓ = 2` is covered) and **not** *"at every
  `ℓ`"* (`ℓ = char F` is not, and there the conclusion is false rather than open).
* ⚠️ **Nothing about the `*Three` or `*Two` files being redundant, and nothing is deleted.**
  `EllipticCurves.TateModule.MatrixRepThree` reaches `ℓ = 3` through `x(3P) = Φ₃/Ψ₃²`
  (`EllipticCurves.Torsion.TriplingSurjective`); this file reaches every prime through
  `#E[n] = n²` and the Wronskian identity. Two independent routes to one conclusion are the
  cheapest cross-check available on both, and the `_three` names are consumed downstream. The
  subsumption at `ℓ = 2` and `ℓ = 3` is a compiled `example` in the *Non-vacuity* section rather
  than a docstring claim.
* **Not surjectivity and not openness of the image.** `EllipticCurves.TateModule.PrimaryImage`
  gives compactness and closedness of `range ρ`; *"the image is open"* is a genuinely different
  theorem and nothing here supplies it. ⚠️ Do not let the word "image" in the neighbouring file
  names suggest otherwise.
* **Not `det ρ_{E,ℓ} = χ_ℓ`.** The `ℓ`-adic cyclotomic-character identity needs the Weil pairing on
  `E[ℓ^k]` for every `k`; this rung supplies matrices, not a pairing. The **mod-`ℓ`** identity is a
  different statement and lives in
  `EllipticCurves.FunctionField.WeilPairingDeterminantCharacter`.
* **Nothing at `ℓ = char F`.**

## The import question, answered before anything was written

`#1533` warns that `EllipticCurves.TateModule.FreeGeneral` imports
`EllipticCurves.TateModule.PrimaryFree`, so any file `PrimaryFree` transitively reaches cannot
import `FreeGeneral` and the instantiation would need a new leaf. Measured by import-closure walk
over `^import` lines: `EllipticCurves.TateModule.PrimaryMatrixRep` is **not** in `FreeGeneral`'s
transitive closure and `FreeGeneral` is **not** in `PrimaryMatrixRep`'s — `PrimaryMatrixRep`'s only
`EllipticCurves` import is `TateModule.GaloisAction`, which is off the `PrimaryFree` path entirely.
So this file could have been either a new leaf or an edit in place; it is a **new leaf** because
that is what keeps the diff additive and out of PR #590's way, not because a cycle forced it.

## Main statements

* `WeierstrassCurve.Affine.tateModule.nonempty_basis_tateModule_of_natCast_ne_zero` :
  `Nonempty (Basis (Fin 2) ℤ_[ℓ] (T_ℓE))` at every prime `ℓ` with `(ℓ : F) ≠ 0`.
* `WeierstrassCurve.Affine.exists_galoisRepMatrix_of_natCast_ne_zero` : a basis of `T_ℓE` and a
  representation `ρ : G →* GL (Fin 2) ℤ_[ℓ]` computing the Galois action exist, at every prime `ℓ`
  with `(ℓ : F) ≠ 0`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7 and VII.7.
-/

open Matrix

namespace WeierstrassCurve.Affine

namespace tateModule

/-! ### A basis of `T_ℓE` indexed by `Fin 2`, at every prime away from the characteristic -/

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} {ℓ : ℕ} [Fact ℓ.Prime]

/-- **`T_ℓE` has a basis indexed by `Fin 2`, at every prime `ℓ` with `(ℓ : F) ≠ 0`.** The basis
itself depends on a choice of coherent system of generating pairs of the `E[ℓ^k]`; its existence
does not.

This is `nonempty_basis_tateModule_three` (`EllipticCurves.TateModule.MatrixRepThree`) with the
`ℓ = 3` input replaced by `nonempty_tateModuleEquivProd_of_natCast_ne_zero`
(`EllipticCurves.TateModule.FreeGeneral`), and it is the only substitution in this file.

⚠️ **Deletion test**, measured on this file as committed. Replacing the argument
`(nonempty_tateModuleEquivProd_of_natCast_ne_zero h2 hl)` by a hole — `by refine
nonempty_basis_tateModule_of_nonempty (W := W) (ℓ := ℓ) ?_` — leaves

```
error: unsolved goals
F : Type u_1
inst✝⁴ : Field F
inst✝³ : DecidableEq F
W : Affine F
ℓ : ℕ
inst✝² : Fact (Nat.Prime ℓ)
inst✝¹ : IsAlgClosed F
inst✝ : WeierstrassCurve.IsElliptic W
h2 : 2 ≠ 0
hl : ↑ℓ ≠ 0
⊢ Nonempty (↥(W.tateModule ℓ) ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])
```

⚠️ Two mechanical changes accompany the deletion and neither adds information: term mode becomes
`by refine … ?_` so that a hole is legal, and `W` and `ℓ` are pinned, which the term-mode form
infers from the expected type. `h2` and `hl` both **survive** in the context, so what is removed is
a construction and not a hypothesis, and the residual is a **goal**, which no type mismatch could
produce. It is exactly `#268`'s theorem — the rank-two input, which is where the whole cost of a
general prime sits. -/
theorem nonempty_basis_tateModule_of_natCast_ne_zero [IsAlgClosed F] [W.IsElliptic]
    (h2 : (2 : F) ≠ 0) (hl : (ℓ : F) ≠ 0) :
    Nonempty (Module.Basis (Fin 2) ℤ_[ℓ] (W.tateModule ℓ)) :=
  nonempty_basis_tateModule_of_nonempty (nonempty_tateModuleEquivProd_of_natCast_ne_zero h2 hl)

end tateModule

/-! ### The matrix representation at every prime away from the characteristic -/

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **The `ℓ`-adic Galois representation exists at every prime `ℓ` with `(ℓ : F) ≠ 0`**, as a matrix
representation that really does compute the Galois action: there are a basis of `T_ℓE` and a
homomorphism `ρ : G →* GL₂(ℤ_[ℓ])` whose matrices act on coordinate vectors the way `G` acts on
`T_ℓE`.

The compatibility clause is the point. `Nonempty ((F ≃ₐ[S] F) →* GL (Fin 2) ℤ_[ℓ])` on its own
would be vacuous — the trivial homomorphism witnesses it, and the statement would not mention the
curve at all.

This is `exists_galoisRepMatrixThree` (`EllipticCurves.TateModule.MatrixRepThree`) with the `ℓ = 3`
input replaced by `nonempty_tateModuleEquivProd_of_natCast_ne_zero`
(`EllipticCurves.TateModule.FreeGeneral`).

⚠️ **Deletion test**, measured on this file as committed. Replacing the argument
`(tateModule.nonempty_tateModuleEquivProd_of_natCast_ne_zero h2 hl)` by a hole — `by refine
exists_galoisRepMatrix_of_nonempty (W' := W') (F := F) (ℓ := ℓ) ?_` — leaves

```
error: unsolved goals
S : Type u_1
F : Type u_2
inst✝⁶ : Field S
inst✝⁵ : Field F
inst✝⁴ : DecidableEq F
inst✝³ : Algebra S F
W' : Affine S
ℓ : ℕ
inst✝² : Fact (Nat.Prime ℓ)
inst✝¹ : IsAlgClosed F
inst✝ : WeierstrassCurve.IsElliptic W'⁄F
h2 : 2 ≠ 0
hl : ↑ℓ ≠ 0
⊢ Nonempty (↥((W'⁄F).tateModule ℓ) ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])
```

⚠️ `h2` and `hl` both **survive**, so the deletion removes a construction and not a hypothesis, and
the residual is a **goal** rather than a type mismatch. It is `T_ℓE ≅ ℤ_ℓ²` itself, which is the
whole content: this is the goal that could not be discharged at `ℓ ≥ 5` before `#268` closed. -/
theorem exists_galoisRepMatrix_of_natCast_ne_zero [IsAlgClosed F] [(W'⁄F).IsElliptic]
    (h2 : (2 : F) ≠ 0) (hl : (ℓ : F) ≠ 0) :
    ∃ (b : Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ))
      (ρ : (F ≃ₐ[S] F) →* GL (Fin 2) ℤ_[ℓ]), ∀ (σ : F ≃ₐ[S] F) (f : (W'⁄F).tateModule ℓ),
        ⇑(b.repr (σ • f)) = (ρ σ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) *ᵥ ⇑(b.repr f) :=
  exists_galoisRepMatrix_of_nonempty
    (tateModule.nonempty_tateModuleEquivProd_of_natCast_ne_zero h2 hl)

/-! ### Non-vacuity

⚠️ `exists_galoisRepMatrix_of_natCast_ne_zero` is an **existential**, so it is the vacuity-prone
kind, and the compatibility clause is what stops it from being witnessed by the trivial
homomorphism. Two things have to be certified, and they are different:

1. that the hypotheses are simultaneously satisfiable on a curve that exists, over a base `S` whose
   absolute Galois group is not trivial — hence `S = ℚ` and `F = ℚ̄` throughout;
2. ⚠️ that the statement is **general** rather than a re-parametrisation of the primes this
   development already reached. `ℓ = 5` alone does not show this: it proves only that `{2, 3}` was
   left. The certificates below therefore run at `ℓ = 5`, `ℓ = 7` **and** `ℓ = 11`, and at `7` and
   `11` on a **second curve** (`y² = x³ + 1`, Δ = −432) that neither this file's own `ℓ = 5` block
   nor `EllipticCurves.TateModule.FreeGeneral` mentions.

⚠️ **On `Fact (Nat.Prime p)` and `private`.** `ℤ_[p]` does not elaborate without it, so it is
needed in the *statements* and cannot be a `haveI` inside a proof; and `Nat.fact_prime_two` /
`Nat.fact_prime_three` have no `Mathlib` counterparts at `5`, `7`, `11`. ⚠️ `private` hides a
**name**, not an **instance** (`#1397`): the three instances below take part in typeclass
resolution in every module downstream of this one. That is harmless — `Fact` is a `Prop`, so a
duplicate is proof-irrelevant — but it is stated here rather than left as a surprise.
`EllipticCurves.TateModule.FreeGeneral` already leaks one at `5`; `factPrimeFiveRep` below is a
deliberate duplicate so that this file's certificates do not silently depend on that accident.

⚠️ `by norm_num` does **not** close `Nat.Prime 5` in this import closure — the `NormNum.Prime`
extension is not reachable — so these use `by decide`. -/

section Nonvacuity

/-! The certificate curves are the shared `EllipticCurves.Fixture.y2AddYEqX3` (`y² + y = x³`, the
standard fixture on this front) and `EllipticCurves.Fixture.y2EqX3AddOne` (`y² = x³ + 1`), both over
`ℚ` and base-changed to `EllipticCurves.Fixture.AlgClosedQ` — algebraically closed so that
`Gal(F/ℚ)` is not the trivial group, and of characteristic `0` so that every `(p : F) ≠ 0` holds.
The base-changed `IsElliptic` instances come from `EllipticCurves.Fixture.instIsEllipticBaseChange`;
this block declares no fixture of its own (`#1408`). -/

open EllipticCurves.Fixture

private instance factPrimeFiveRep : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance factPrimeSevenRep : Fact (Nat.Prime 7) := ⟨by decide⟩
private instance factPrimeElevenRep : Fact (Nat.Prime 11) := ⟨by decide⟩

private lemma exampleTwoRep : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleFiveRep : ((5 : ℕ) : AlgClosedQ) ≠ 0 := by
  have : ((5 : ℕ) : AlgClosedQ) = 5 := by push_cast; ring
  rw [this]; norm_num

private lemma exampleSevenRep : ((7 : ℕ) : AlgClosedQ) ≠ 0 := by
  have : ((7 : ℕ) : AlgClosedQ) = 7 := by push_cast; ring
  rw [this]; norm_num

private lemma exampleElevenRep : ((11 : ℕ) : AlgClosedQ) ≠ 0 := by
  have : ((11 : ℕ) : AlgClosedQ) = 11 := by push_cast; ring
  rw [this]; norm_num

open Classical in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on a curve that exists, over a base field `S = ℚ` whose
absolute Galois group is not trivial, `ρ_{E,5}` really is a `GL₂(ℤ_[5])`-valued representation that
computes the Galois action.

`5` is the first prime at which no earlier statement in this development produces a matrix
representation: `EllipticCurves.TateModule.MatrixRep` is `ℓ = 2` and
`EllipticCurves.TateModule.MatrixRepThree` is `ℓ = 3`.

⚠️ The statement is restated in full rather than obtained-and-projected (`#916`), and the
compatibility clause `⇑(b.repr (σ • f)) = ρ σ *ᵥ ⇑(b.repr f)` is kept — without it the certificate
would be witnessed by the trivial homomorphism and would not mention the curve. -/
example : ∃ (b : Module.Basis (Fin 2) ℤ_[5] (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 5))
    (ρ : (AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) →* GL (Fin 2) ℤ_[5]),
      ∀ (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ)
        (f : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 5),
        ⇑(b.repr (σ • f)) = (ρ σ : Matrix (Fin 2) (Fin 2) ℤ_[5]) *ᵥ ⇑(b.repr f) :=
  exists_galoisRepMatrix_of_natCast_ne_zero exampleTwoRep exampleFiveRep

open Classical in
/-- **The module the matrices act on is not the zero module**, on the same curve at `ℓ = 5`, by a
route that never mentions the matrix representation: `T₅E` surjects onto `E[5^k]`, which has `25^k`
elements.

⚠️ This is what rules out the degenerate reading of the certificate above. `GL (Fin 2) ℤ_[5]` and
the `mulVec` clause are both perfectly satisfiable over a zero module — every coordinate vector
would be `0` and the equation would hold for any `ρ` — so the certificate needs this. -/
example : Infinite (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 5) :=
  tateModule.infinite_tateModule_of_card (Fact.out : (5 : ℕ).Prime).one_lt
    (tateModule.proj_surjective_of_two_ne_zero exampleTwoRep)
    (card_torsion_pow_mul_self_of_natCast_ne_zero exampleTwoRep exampleFiveRep)

open Classical in
/-- ⚠️ **`ℓ = 7` and `ℓ = 11`, on a SECOND curve.** `y² = x³ + 1` (Δ = −432) is not the fixture the
`ℓ = 5` block above uses, and neither prime is mentioned anywhere in the chain this file consumes.
This is the certificate that the general statement is not `{2, 3, 5}`-parametrised — which `ℓ = 5`
alone cannot show. -/
example : (∃ (b : Module.Basis (Fin 2) ℤ_[7] (((y2EqX3AddOne ℚ)⁄AlgClosedQ).tateModule 7))
      (ρ : (AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) →* GL (Fin 2) ℤ_[7]),
        ∀ (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ)
          (f : ((y2EqX3AddOne ℚ)⁄AlgClosedQ).tateModule 7),
          ⇑(b.repr (σ • f)) = (ρ σ : Matrix (Fin 2) (Fin 2) ℤ_[7]) *ᵥ ⇑(b.repr f)) ∧
    ∃ (b : Module.Basis (Fin 2) ℤ_[11] (((y2EqX3AddOne ℚ)⁄AlgClosedQ).tateModule 11))
      (ρ : (AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) →* GL (Fin 2) ℤ_[11]),
        ∀ (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ)
          (f : ((y2EqX3AddOne ℚ)⁄AlgClosedQ).tateModule 11),
          ⇑(b.repr (σ • f)) = (ρ σ : Matrix (Fin 2) (Fin 2) ℤ_[11]) *ᵥ ⇑(b.repr f) :=
  ⟨exists_galoisRepMatrix_of_natCast_ne_zero exampleTwoRep exampleSevenRep,
    exists_galoisRepMatrix_of_natCast_ne_zero exampleTwoRep exampleElevenRep⟩

open Classical in
/-- ⚠️ **The subsumption of `EllipticCurves.TateModule.MatrixRep` (`ℓ = 2`) and
`EllipticCurves.TateModule.MatrixRepThree` (`ℓ = 3`), machine-checked.** Both conclusions are
re-derived from the general statement alone, on the fixture those files use — so *"this is at least
as wide as the two special cases"* is a compiled claim and not a docstring assertion.

⚠️ It does **not** follow that those files are redundant, and nothing is deleted: they reach `ℓ = 2`
and `ℓ = 3` by routes this one does not use (tangent-line doubling; `x(3P) = Φ₃/Ψ₃²`), so each is a
check on the other, and the `_two` / `_three` names are consumed downstream. -/
example : Nonempty (Module.Basis (Fin 2) ℤ_[2] (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 2)) ∧
    Nonempty (Module.Basis (Fin 2) ℤ_[3] (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 3)) :=
  ⟨tateModule.nonempty_basis_tateModule_of_natCast_ne_zero exampleTwoRep
      (by exact_mod_cast exampleTwoRep),
    tateModule.nonempty_basis_tateModule_of_natCast_ne_zero exampleTwoRep
      (by have : ((3 : ℕ) : AlgClosedQ) = 3 := by push_cast; ring
          rw [this]; exact three_ne_zero_of_charZero _)⟩

end Nonvacuity

end WeierstrassCurve.Affine
