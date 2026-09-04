/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.WeilPairingDeterminantCharacter
import EllipticCurves.TateModule.MatrixRepMod

/-!
# `det ρ_{E,3} = χ_3` for the **matrix** representation `G →* GL₂(ℤ/3)`

Two merged files hold the two halves of this statement, one directory apart, and neither may hold
the composition:

* `EllipticCurves.TateModule.MatrixRepMod` (`#1242`) has `det_comp_galoisRepModMatrix`, which says
  the determinant of the *matrix* representation attached to a basis `b` of `E[3]` is the
  basis-free character `galoisDetMod 3`;
* `EllipticCurves.FunctionField.WeilPairingDeterminantCharacter` (`#958`) has
  `galoisDetMod_three_eq_galoisModularCyclotomicChar`, which says that character is `χ_3`.

`MatrixRepMod`'s own `## Scope` section says why it cannot host the composition — *"composing the
two is a statement for a `FunctionField/` file, not for this one"* — and this is that file.  The
direction is deliberate and was re-verified rather than assumed: **no module under `TateModule/`
imports anything under `FunctionField/`**, and `MatrixRepMod` is **not** in
`WeilPairingDeterminantCharacter`'s import closure either (measured in Python over the project's
own `import` lines, both directions; the closures are 39 and 168 modules and neither contains the
other).  So this file imports both, and it is a **leaf**: nothing under `TateModule/` may import
it.

```
det ∘ ρ_{E,3} = χ_3   as monoid homomorphisms  Gal(F/S) →* (ZMod 3)ˣ.
```

## ⚠️ Why a one-`rw` composition is worth a file

Neither input mentions a matrix and the cyclotomic character in the same sentence.  What an
arithmetic consumer holds is a `GL (Fin 2) (ZMod 3)`-valued representation and the determinant of a
`2 × 2` matrix; `galoisDetMod` is `LinearEquiv.det` of a bundled linear equivalence and is the
object neither of them has in hand.  The composition is the sentence *"the determinant of the
matrix of `σ` acting on `E[3]` is the cyclotomic character"*, and until it is stated it is a
sentence this tree does not contain.

## The consequence that is genuinely new, and is not about `galoisDetMod`

`range_galoisRepModMatrix_three_not_le_range_toGL`: given one `σ` with `χ_3(σ) ≠ 1`, the image of
`ρ_{E,3}` is **not** contained in `SL₂(ℤ/3)` — stated as
`¬ (galoisRepModMatrix b).range ≤ (Matrix.SpecialLinearGroup.toGL).range`, which is that inclusion
written with Mathlib's embedding of `SLₙ` in `GLₙ`.  That is a statement about the matrix
representation and about a *subgroup of matrices*; `galoisDetMod_three_ne_one_of_…` cannot express
it, because nothing in `TateModule.DeterminantMod` has a `SpecialLinearGroup` in it.  It is fired
unconditionally on a curve over `ℚ` in the non-vacuity block below.

## ⚠️ Basis-independence is free here and no lemma is added for it

`galoisRepModMatrix` takes the basis as an explicit argument, so every statement below mentions a
`b`.  None of the *conclusions* does: the right-hand side is `χ_3`, which mentions no basis, so
each theorem below holds **for every** `b` — that is how they are stated, universally quantified
over the basis, rather than for a chosen one.  This is `det_galoisRepModMatrix`'s own argument
(*"it also settles basis-independence of the determinant, since the right-hand side does not
mention `b`"*) transported one level up, and it is why `galoisRepModMatrix_conj`
(`EllipticCurves.TateModule.MatrixRepMod`) is **cited and not restated**: the conjugacy is what
makes basis-dependent objects usable, and the determinant is a conjugation invariant, but no step
below needs to say so out loud.

## Main statements

Every public declaration of this file is listed here, and all are in namespace
`WeierstrassCurve.Affine`.

* `det_galoisRepModMatrix_three_eq_galoisModularCyclotomicChar` — the pointwise identity,
  `det (ρ_b(σ)) = χ_3(σ)` in `(ZMod 3)ˣ`, at every basis `b` and every `σ`;
* `det_comp_galoisRepModMatrix_three_eq_galoisModularCyclotomicChar` — the same as an identity of
  monoid homomorphisms `Gal(F/S) →* (ZMod 3)ˣ`;
* `exists_galoisRepModMatrix_three_det_eq_galoisModularCyclotomicChar` — the choice-free form:
  `exists_galoisRepModMatrix_three` (`EllipticCurves.TateModule.MatrixRepMod`) with its fourth
  conjunct `det (ρ σ) = galoisDetMod 3 σ` replaced by `det (ρ σ) = χ_3(σ)`, so that a consumer with
  no basis in hand gets a representation, its computation rule, and the arithmetic identification
  together;
* `det_galoisRepModMatrix_three_ne_one_of_galoisModularCyclotomicChar_ne_one` — the non-triviality
  transfer;
* `range_galoisRepModMatrix_three_not_le_range_toGL` — the image is not contained in `SL₂(ℤ/3)`.

## What is *not* here

* **Nothing at `n = 2`.**  `EllipticCurves.FunctionField.WeilPairingDeterminantCharacter` explains
  why `galoisDetMod 2 = χ_2` is content-free — `(ZMod 2)ˣ` is a subsingleton, so both sides are
  constantly `1` and the equation holds of any pair of characters into it.  The matrix form inherits
  exactly that, so it is not stated either.
* **Nothing at general `3`-smooth `n`**, even though `galoisRepModMatrix` is defined at every `n`
  with `[NeZero n]` and `basisTorsionOfSmooth` supplies a basis at every `3`-smooth `n > 1`.  What
  confines this to `n = 3` is the **pairing**: `weilPairingThree` and its `n = 2` twin are all this
  development has, and `#1240`'s rank statement manufactures no more.  ⚠️ It is *not* the
  representation, the basis or the determinant that is missing at `n = 12`; all three exist and
  `EllipticCurves.TateModule.MatrixRepMod` commits certificates for them there.
* **Not the `ℓ`-adic statement.**  `galoisDetTwo = χ_2` over `ℤ_[2]` needs the pairing on `E[2 ^ k]`
  at every level and is untouched, as `WeilPairingDeterminantCharacter` already records.
* **`#951` is not subsumed and is not touched.**
  `EllipticCurves.FunctionField.WeilPairingDeterminant` states `a * d − b * c ≡ χ_3(σ)` with the
  four entries carried as integers in hypotheses relative to a chosen pairing-generating pair.
  `MatrixRepMod`'s Scope section gives the structural reason the two do not subsume each other and
  it is unchanged by this file: a pairing basis exists only where the pairing does, and
  `galoisRepModMatrix` is defined for *every* basis.
* **No trace, no characteristic polynomial, no `Gal(F/S)`-stable basis.**  Three files record that
  the first two have no consumer and that the third does not exist in general; none of that is
  retired here.
* **No new Weil-pairing mathematics.**  `#957`'s `e_n(α x, α y) = e_n(x, y) ^ det α` remains a
  detour for the reason `WeilPairingDeterminantCharacter` gives: `LinearMap.det_toMatrix` already
  performs the reduction.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.1(a), (b), (d), and
  III.8.6.
-/

namespace WeierstrassCurve.Affine

open CoordinateRing Matrix

section Galois

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S} [W.IsElliptic]
  [IsAlgClosed F]

/-! ### The composition

⚠️ **`[DecidableEq F]` is supplied by `open Classical in` on every declaration, not by a section
variable**, because that is what `EllipticCurves.FunctionField.WeilPairingDeterminantCharacter`
does and the two sides have to agree on the instance for `galoisDetMod` to be the *same* term in
both.  `EllipticCurves.TateModule.MatrixRepMod` takes `[DecidableEq F]` as a section variable
instead; declaring one here would make `det_galoisRepModMatrix`'s statement and
`galoisDetMod_three_apply_eq_galoisModularCyclotomicChar`'s statement about two different terms. -/

open Classical in
/-- **`det (ρ_{E,3}(σ)) = χ_3(σ)`** in `(ZMod 3)ˣ`, for the matrix representation attached to any
`ZMod 3`-basis `b` of `E[3]` — Silverman *AEC* III.8.1(a), (b) and (d) in the form a consumer
holding a matrix can use.

Two merged halves, composed: `det_galoisRepModMatrix` (`EllipticCurves.TateModule.MatrixRepMod`)
identifies the determinant of the matrix with the basis-free `galoisDetMod 3`, and
`galoisDetMod_three_apply_eq_galoisModularCyclotomicChar`
(`EllipticCurves.FunctionField.WeilPairingDeterminantCharacter`) identifies that with `χ_3`.

⚠️ The conclusion does not mention `b`, so this holds at **every** basis; see the module docstring
for why no basis-independence lemma is added. -/
theorem det_galoisRepModMatrix_three_eq_galoisModularCyclotomicChar
    (b : Module.Basis (Fin 2) (ZMod 3) ((W⁄F).torsion 3)) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (σ : F ≃ₐ[S] F) :
    Matrix.GeneralLinearGroup.det (galoisRepModMatrix b σ)
      = galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_ne_zero h3) σ := by
  rw [det_galoisRepModMatrix, galoisDetMod_three_apply_eq_galoisModularCyclotomicChar σ h2 h3]

open Classical in
/-- **`det ∘ ρ_{E,3} = χ_3` as an identity of monoid homomorphisms** `Gal(F/S) →* (ZMod 3)ˣ` — the
matrix form of `galoisDetMod_three_eq_galoisModularCyclotomicChar`.

This is the form to quote when the point is that the *character* is cyclotomic and not merely each
of its values, which is the distinction
`det_comp_galoisRepModMatrix` (`EllipticCurves.TateModule.MatrixRepMod`) draws one level down. -/
theorem det_comp_galoisRepModMatrix_three_eq_galoisModularCyclotomicChar
    (b : Module.Basis (Fin 2) (ZMod 3) ((W⁄F).torsion 3)) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    (Matrix.GeneralLinearGroup.det : GL (Fin 2) (ZMod 3) →* (ZMod 3)ˣ).comp
        (galoisRepModMatrix b)
      = galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_ne_zero h3) :=
  MonoidHom.ext (det_galoisRepModMatrix_three_eq_galoisModularCyclotomicChar b h2 h3)

open Classical in
/-- **The choice-free form**: there is a `ZMod 3`-basis of `E[3]` and a representation
`Gal(F/S) →* GL₂(ℤ/3)` which computes the Galois action on coordinates and whose determinant is
`χ_3`.

⚠️ This is `exists_galoisRepModMatrix_three` (`EllipticCurves.TateModule.MatrixRepMod`) with its
**fourth conjunct** `det (ρ σ) = galoisDetMod 3 σ` replaced by `det (ρ σ) = χ_3(σ)`, and it is
stated in the same pointwise shape so that the two are read side by side; the homomorphism-level
form is `det_comp_galoisRepModMatrix_three_eq_galoisModularCyclotomicChar` above.  It is the
statement for a consumer that has no basis in hand, and it is what makes this a theorem about the
curve rather than about a chosen basis. -/
theorem exists_galoisRepModMatrix_three_det_eq_galoisModularCyclotomicChar
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ∃ (c : Module.Basis (Fin 2) (ZMod 3) ((W⁄F).torsion 3))
      (ρ : (F ≃ₐ[S] F) →* GL (Fin 2) (ZMod 3)),
      (∀ (σ : F ≃ₐ[S] F) (P : (W⁄F).torsion 3),
        ⇑(c.repr (σ • P)) = (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ ⇑(c.repr P)) ∧
      ∀ σ : F ≃ₐ[S] F, Matrix.GeneralLinearGroup.det (ρ σ)
        = galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_ne_zero h3) σ :=
  ⟨basisTorsionThree (W := W⁄F) h2 h3, galoisRepModMatrix _, galoisRepModMatrix_mulVec _,
    det_galoisRepModMatrix_three_eq_galoisModularCyclotomicChar _ h2 h3⟩

/-! ### The image is not contained in `SL₂(ℤ/3)`

⚠️ **This is the part that is not a restatement of anything under `TateModule/`.**  The two
statements below are about the *matrix* representation and, in the second, about a subgroup of
matrices; `galoisDetMod_three_ne_one_of_galoisModularCyclotomicChar_ne_one`
(`EllipticCurves.FunctionField.WeilPairingDeterminantCharacter`) is their input and cannot express
either, since `EllipticCurves.TateModule.DeterminantMod` has no matrix and no
`Matrix.SpecialLinearGroup` in it. -/

open Classical in
/-- **If `χ_3(σ) ≠ 1` then `det (ρ_{E,3}(σ)) ≠ 1`**, over a field with `(2 : F) ≠ 0` and
`(3 : F) ≠ 0`, for the matrix representation at any basis.

`#947`'s `exists_galoisModularCyclotomicChar_three_ne_one` produces such a `σ` over `ℚ`
unconditionally; the non-vacuity block below fires it. -/
theorem det_galoisRepModMatrix_three_ne_one_of_galoisModularCyclotomicChar_ne_one
    (b : Module.Basis (Fin 2) (ZMod 3) ((W⁄F).torsion 3)) {σ : F ≃ₐ[S] F}
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hσ : galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_ne_zero h3) σ ≠ 1) :
    Matrix.GeneralLinearGroup.det (galoisRepModMatrix b σ) ≠ 1 := by
  rw [det_galoisRepModMatrix_three_eq_galoisModularCyclotomicChar b h2 h3]
  exact hσ

open Classical in
/-- **The image of `ρ_{E,3}` is not contained in `SL₂(ℤ/3)`**, over a field with `(2 : F) ≠ 0` and
`(3 : F) ≠ 0`, as soon as one `σ` has `χ_3(σ) ≠ 1` — and at **every** basis `b`, since `hσ`
mentions none.

The inclusion is written as `(galoisRepModMatrix b).range ≤ (Matrix.SpecialLinearGroup.toGL).range`
with Mathlib's monoid embedding `SLₙ(R) →* GLₙ(R)`, so the statement is literally *"every matrix in
the image has determinant `1`"* negated.

⚠️ **This is the sentence the composition was worth stating for.**  It is about the matrix
representation and about a subgroup of matrices, and neither half on its own can say it: the
`TateModule/` side has no `χ_3`, and the `FunctionField/` side has no matrix. -/
theorem range_galoisRepModMatrix_three_not_le_range_toGL
    (b : Module.Basis (Fin 2) (ZMod 3) ((W⁄F).torsion 3)) {σ : F ≃ₐ[S] F}
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hσ : galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_ne_zero h3) σ ≠ 1) :
    ¬ (galoisRepModMatrix b).range ≤
      (SpecialLinearGroup.toGL (n := Fin 2) (R := ZMod 3)).range := by
  intro hle
  obtain ⟨A, hA⟩ := hle ⟨σ, rfl⟩
  refine det_galoisRepModMatrix_three_ne_one_of_galoisModularCyclotomicChar_ne_one b h2 h3 hσ ?_
  rw [← hA]
  ext
  simp [SpecialLinearGroup.toGL]

end Galois

/-! ### Non-vacuity

The curve is this front's standard `n = 3` certificate curve, `y² + y = x³` over `ℚ` base-changed
to `AlgebraicClosure ℚ`, with **`S = ℚ` and not `S = F`** — over `S = F` the group `Gal(F/S)` is
trivial and a certificate about a Galois *representation* says nothing.  Every hypothesis is
produced, not assumed.

⚠️ **The load-bearing certificate is the last one, and it is unconditional**: on that curve the
image of `ρ_{E,3}` is not contained in `SL₂(ℤ/3)`, for **every** `ZMod 3`-basis of `E[3]`.  No `σ`
is assumed and no rationality is assumed; the input is `#947`'s theorem that `χ_3` of `ℚ` is not
trivial.  Every other statement in this file, and every statement in
`EllipticCurves.TateModule.MatrixRepMod`, is satisfied verbatim by a representation landing in
`SL₂`; this one is not.

⚠️ **It was tested by deleting its last named lemma** (`#944`, the idiom
`EllipticCurves.FunctionField.WeilPairingDeterminantCharacter` documents).  Deleting the
`exact range_galoisRepModMatrix_three_not_le_range_toGL …` line, leaving the rest of the script
untouched, gives

```
error: unsolved goals
σ : Gal(AlgebraicClosure ℚ/ℚ)
hσ : (galoisModularCyclotomicChar ℚ (AlgebraicClosure ℚ) ⋯) σ ≠ 1
⊢ ∀ (c : Module.Basis (Fin 2) (ZMod 3) ↥(((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3)),
    ¬(galoisRepModMatrix c).range ≤ SpecialLinearGroup.toGL.range
```

⚠️ **Read the hypothesis list, not the error tag**: what survives is a statement about `χ_3` and a
goal about matrices, with *nothing relating them*.  The certificate is closed by this file's
identity and by nothing else.

⚠️ **There is deliberately no certificate in which `E[3]` is `ℚ`-rational**, and the reason is not
that none was looked for: `#947`'s `ker_galoisRepMod_three_le_ker_galoisModularCyclotomicChar`
*rules one out* over `ℚ`, since `E[3] ⊆ E(ℚ)` would force `χ_3` of `ℚ` to be trivial.
`EllipticCurves.FunctionField.WeilPairingDeterminantCharacter` records this at length; it is
repeated here only because a reader of *this* file would otherwise ask for one. -/

section Nonvacuity

/-! The certificate curve `y² + y = x³` is the shared `EllipticCurves.Fixture.y2AddYEqX3`, and the
base — algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here. -/

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

open Classical in
/-- A `ZMod 3`-basis of `E[3]` on the certificate curve, fixed once so that the pointwise
certificates below speak about the same representation.  ⚠️ The load-bearing certificate does
**not** use it: it quantifies over all bases. -/
private noncomputable def exampleBasisThree :
    Module.Basis (Fin 2) (ZMod 3) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3) :=
  basisTorsionThree exampleTwo exampleThree

open Classical in
/-- The headline on a curve that exists, at a fixed basis and an arbitrary `σ`. -/
example (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) :
    Matrix.GeneralLinearGroup.det (galoisRepModMatrix exampleBasisThree σ)
      = galoisModularCyclotomicChar ℚ AlgClosedQ
          (natCard_rootsOfUnity_of_ne_zero (F := AlgClosedQ) (n := 3) exampleThree) σ :=
  det_galoisRepModMatrix_three_eq_galoisModularCyclotomicChar
    (W := y2AddYEqX3 ℚ) exampleBasisThree exampleTwo exampleThree σ

open Classical in
/-- The choice-free form on the same curve: a basis, a matrix representation computing the Galois
action, and `det = χ_3`, all produced. -/
example : ∃ (c : Module.Basis (Fin 2) (ZMod 3) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3))
      (ρ : (AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) →* GL (Fin 2) (ZMod 3)),
      (∀ (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ)
        (P : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3),
        ⇑(c.repr (σ • P)) = (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ ⇑(c.repr P)) ∧
      ∀ σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ, Matrix.GeneralLinearGroup.det (ρ σ)
        = galoisModularCyclotomicChar ℚ AlgClosedQ
            (natCard_rootsOfUnity_of_ne_zero (F := AlgClosedQ) (n := 3) exampleThree) σ :=
  exists_galoisRepModMatrix_three_det_eq_galoisModularCyclotomicChar exampleTwo exampleThree

open Classical in
/-- Some `σ ∈ Gal(ℚ̄/ℚ)` has `det (ρ_{E,3}(σ)) ≠ 1` — the existential form, weaker than the
certificate below. -/
example : ∃ σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ,
    Matrix.GeneralLinearGroup.det (galoisRepModMatrix exampleBasisThree σ) ≠ 1 := by
  obtain ⟨σ, hσ⟩ := exists_galoisModularCyclotomicChar_three_ne_one
    (natCard_rootsOfUnity_of_ne_zero (F := AlgClosedQ) (n := 3) exampleThree)
  exact ⟨σ, det_galoisRepModMatrix_three_ne_one_of_galoisModularCyclotomicChar_ne_one
    (W := y2AddYEqX3 ℚ) exampleBasisThree exampleTwo exampleThree hσ⟩

open Classical in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on `y² + y = x³` over `ℚ`, the image of the mod-`3` matrix
representation `Gal(ℚ̄/ℚ) →* GL₂(ℤ/3)` is **not** contained in `SL₂(ℤ/3)` — at every `ZMod 3`-basis
of `E[3]`, unconditionally. -/
example : ∀ c : Module.Basis (Fin 2) (ZMod 3) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3),
    ¬ (galoisRepModMatrix (S := ℚ) c).range
      ≤ (SpecialLinearGroup.toGL (n := Fin 2) (R := ZMod 3)).range := by
  obtain ⟨σ, hσ⟩ := exists_galoisModularCyclotomicChar_three_ne_one
    (natCard_rootsOfUnity_of_ne_zero (F := AlgClosedQ) (n := 3) exampleThree)
  exact fun c => range_galoisRepModMatrix_three_not_le_range_toGL
    (W := y2AddYEqX3 ℚ) c exampleTwo exampleThree hσ

end Nonvacuity

end WeierstrassCurve.Affine
