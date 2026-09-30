/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.WeilPairingDeterminantCharacterN
import EllipticCurves.TateModule.MatrixRepMod

/-!
# `det ρ_{E,n} = χ_n` for the **matrix** representation `G →* GL₂(ℤ/n)`, at a general index

The matrix reading of `EllipticCurves.FunctionField.WeilPairingDeterminantCharacterN`, and the
general-index form of `EllipticCurves.FunctionField.MatrixRepDeterminantCharacter` (`#1243`).  Two
merged halves, composed: `det_galoisRepModMatrix` (`EllipticCurves.TateModule.MatrixRepMod`)
identifies the determinant of the matrix of `ρ_{E,n}(σ)` with the basis-free `galoisDetMod n`, and
`galoisDetMod_n_apply_eq_galoisModularCyclotomicChar` identifies that with `χ_n(σ)`.

## ⚠️ Basis-independence is free and no lemma is added for it

`galoisRepModMatrix` takes the basis as an explicit argument, so every *statement* below mentions a
`b`; none of the *conclusions* does, the right-hand side being `χ_n`.  They are stated universally
quantified over `b`, which is the whole of what a basis-independence lemma would say.

## ⚠️ The choice-free form is built on the PAIRING basis, and that is what removes `1 < n`

`exists_galoisRepModMatrix_n_det_eq_galoisModularCyclotomicChar` produces its basis from
`basisTorsionNOfPairing` at a primitive pair supplied by `exists_orderOf_weilPairingN_eq`, both of
which carry only `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`.

⚠️ **So `EllipticCurves.TateModule.MatrixRepModGeneral` is NOT imported, and that is a measurement
rather than an oversight.**  Its `exists_galoisRepModMatrix_of_natCast_ne_zero` is the same
existential with `galoisDetMod n σ` in place of `χ_n(σ)`, and it binds `1 < n`, because its basis is
`basisTorsionOfNatCastNeZero` and that one is built from a rank.  Nothing of it is used here by
name, so nothing of it is imported.  Measured over project modules only, at the head this file was
written against (`7ba33ed`), counting each module's own import closure including itself: this file
reaches **247** modules and `MatrixRepModGeneral` reaches **77**, and the two are **incomparable** —
exactly **2** modules lie in the second closure and not in the first, namely `MatrixRepModGeneral`
itself and `EllipticCurves.TateModule.DeterminantModGeneral`.

⚠️ **Read that as a statement about hypotheses and not about strength.**  The existential below is
the weaker-hypothesis one; it is not a *stronger* statement, because at `n = 1` — the only index the
two disagree on — every group in sight is trivial and both are content-free.

## ⚠️ The direction of the import is not negotiable, and it is re-verified rather than assumed

No module under `TateModule/` imports anything under `FunctionField/`.  ⚠️ **The clause that would
be the natural citation here is RETIRED in its own source, so it is not cited as live.**
`EllipticCurves.TateModule.MatrixRepMod`'s `## Scope` no longer ends its first paragraph with
*"composing the two is a statement for a `FunctionField/` file, not for this one"*; the next
paragraph quotes that clause and says it *"has been acted on and is RETIRED"*, the actor being the
`n = 3` composition in `EllipticCurves.FunctionField.MatrixRepDeterminantCharacter`.  What that
retirement paragraph writes in its place is what the placement here rests on, and both halves of it
are live: that file is a leaf — *"nothing here or elsewhere under `TateModule/` imports it"* — and
the reason is that its consequence *"needs a matrix and a `Matrix.SpecialLinearGroup` and therefore
cannot live under `TateModule/` either"*, which is exactly what this file's
**### The image is not contained in `SL₂(ℤ/n)`** block below claims for itself.  ⚠️ The placement
conclusion is unchanged; only its attribution was retired text.  Grepped at `7ba33ed`, the head this
file was written against:
`grep -rn 'import EllipticCurves.FunctionField' EllipticCurves/TateModule/` returns **0** lines.
This file and `WeilPairingDeterminantCharacterN` are both **leaves**; nothing under `TateModule/`
may import either.

## ⚠️ `[DecidableEq F]` comes from `open Classical in` and not from a section variable

That is what `EllipticCurves.FunctionField.WeilPairingDeterminantCharacterN` does, and the two sides
have to agree on the instance for `galoisDetMod` to be the *same* term in both.
`EllipticCurves.TateModule.MatrixRepMod` takes `[DecidableEq F]` as a section variable instead;
declaring one here would make `det_galoisRepModMatrix`'s statement and
`galoisDetMod_n_apply_eq_galoisModularCyclotomicChar`'s statement about two different terms.
`#1243` records the same constraint at `n = 3`.

## Main statements

* `WeierstrassCurve.Affine.det_galoisRepModMatrix_n_eq_galoisModularCyclotomicChar` — pointwise, at
  every basis `b` and every `σ`.
* `WeierstrassCurve.Affine.det_comp_galoisRepModMatrix_n_eq_galoisModularCyclotomicChar` — the same
  as an identity of monoid homomorphisms.
* `WeierstrassCurve.Affine.exists_galoisRepModMatrix_n_det_eq_galoisModularCyclotomicChar` — the
  choice-free form: a basis, a representation computing the Galois action on coordinates, and
  `det = χ_n`, all produced.
* `WeierstrassCurve.Affine.det_galoisRepModMatrix_n_ne_one_of_galoisModularCyclotomicChar_ne_one`.
* `WeierstrassCurve.Affine.range_galoisRepModMatrix_n_not_le_range_toGL` — given one `σ` with
  `χ_n(σ) ≠ 1`, the image of `ρ_{E,n}` is **not** contained in `SL₂(ℤ/n)`.

## ⚠️ `n = 2` and `n = 1` are subsumed, not excluded

`det ∘ ρ_{E,2} = χ_2` is **content-free**: `(ZMod 2)ˣ` is a subsingleton, so both sides are
constantly `1` and the equation holds of any pair of characters into it.  `#1243` declines to state
the matrix form at `n = 2` for exactly that reason.  A general-`n` statement **subsumes** a
degenerate index rather than omitting it, so nothing is excluded below — and nothing below may be
read as *strengthening* anything at those two indices, where there is nothing to strengthen.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.1(a), (b), (d), and
  III.8.6.
-/
namespace WeierstrassCurve.Affine

open CoordinateRing Matrix

section Galois

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S} [W.IsElliptic]
  [IsAlgClosed F]

open Classical in
/-- **`det (ρ_{E,n}(σ)) = χ_n(σ)`** in `(ZMod n)ˣ`, for the matrix representation attached to any
`ZMod n`-basis `b` of `E[n]` — Silverman *AEC* III.8.1(a), (b) and (d) in the form a consumer
holding a matrix can use, at every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` over an
algebraically closed `F`.

⚠️ The conclusion does not mention `b`, so this holds at **every** basis; see the module docstring
for why no basis-independence lemma is added. -/
theorem det_galoisRepModMatrix_n_eq_galoisModularCyclotomicChar {n : ℕ} [NeZero n]
    (b : Module.Basis (Fin 2) (ZMod n) ((W⁄F).torsion n)) (h2 : (2 : F) ≠ 0)
    (hn : ((n : ℤ) : F) ≠ 0) (σ : F ≃ₐ[S] F) :
    Matrix.GeneralLinearGroup.det (galoisRepModMatrix b σ)
      = galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_intCast_ne_zero hn) σ := by
  rw [det_galoisRepModMatrix, galoisDetMod_n_apply_eq_galoisModularCyclotomicChar σ h2 hn]

open Classical in
/-- **`det ∘ ρ_{E,n} = χ_n` as an identity of monoid homomorphisms** `Gal(F/S) →* (ZMod n)ˣ` — the
matrix form of `galoisDetMod_n_eq_galoisModularCyclotomicChar`.

This is the form to quote when the point is that the *character* is cyclotomic and not merely each
of its values, which is the distinction `det_comp_galoisRepModMatrix`
(`EllipticCurves.TateModule.MatrixRepMod`) draws one level down. -/
theorem det_comp_galoisRepModMatrix_n_eq_galoisModularCyclotomicChar {n : ℕ} [NeZero n]
    (b : Module.Basis (Fin 2) (ZMod n) ((W⁄F).torsion n)) (h2 : (2 : F) ≠ 0)
    (hn : ((n : ℤ) : F) ≠ 0) :
    (Matrix.GeneralLinearGroup.det : GL (Fin 2) (ZMod n) →* (ZMod n)ˣ).comp
        (galoisRepModMatrix b)
      = galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_intCast_ne_zero hn) :=
  MonoidHom.ext (det_galoisRepModMatrix_n_eq_galoisModularCyclotomicChar b h2 hn)

open Classical in
/-- **The choice-free form**: there is a `ZMod n`-basis of `E[n]` and a representation
`Gal(F/S) →* GL₂(ℤ/n)` which computes the Galois action on coordinates and whose determinant is
`χ_n`.

⚠️ This is `exists_galoisRepModMatrix_of_natCast_ne_zero`
(`EllipticCurves.TateModule.MatrixRepModGeneral`) with its **fourth conjunct**
`det (ρ σ) = galoisDetMod n σ` replaced by `det (ρ σ) = χ_n(σ)`, and it is stated in the same
pointwise shape so that the two are read side by side.  ⚠️ **It is not proved from it and does not
import it**: the basis here is `basisTorsionNOfPairing` at a primitive pair, which is why `1 < n` is
absent.  The module docstring measures the two closures.

It is the statement for a consumer that has no basis in hand, and it is what makes this a theorem
about the curve rather than about a chosen basis. -/
theorem exists_galoisRepModMatrix_n_det_eq_galoisModularCyclotomicChar {n : ℕ} [NeZero n]
    (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0) :
    ∃ (c : Module.Basis (Fin 2) (ZMod n) ((W⁄F).torsion n))
      (ρ : (F ≃ₐ[S] F) →* GL (Fin 2) (ZMod n)),
      (∀ (σ : F ≃ₐ[S] F) (P : (W⁄F).torsion n),
        ⇑(c.repr (σ • P)) = (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod n)) *ᵥ ⇑(c.repr P)) ∧
      ∀ σ : F ≃ₐ[S] F, Matrix.GeneralLinearGroup.det (ρ σ)
        = galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_intCast_ne_zero hn) σ := by
  obtain ⟨P, T, horder⟩ := exists_orderOf_weilPairingN_eq (W := W⁄F) h2 hn
  exact ⟨basisTorsionNOfPairing h2 hn horder, galoisRepModMatrix _,
    galoisRepModMatrix_mulVec _,
    det_galoisRepModMatrix_n_eq_galoisModularCyclotomicChar _ h2 hn⟩

/-! ### The image is not contained in `SL₂(ℤ/n)`

⚠️ **This is the part that is not a restatement of anything under `TateModule/`.**  The two
statements below are about the *matrix* representation and, in the second, about a subgroup of
matrices; `galoisDetMod_n_ne_one_of_galoisModularCyclotomicChar_ne_one`
(`EllipticCurves.FunctionField.WeilPairingDeterminantCharacterN`) is their input and cannot express
either, since `EllipticCurves.TateModule.DeterminantMod` has no matrix and no
`Matrix.SpecialLinearGroup` in it. -/

open Classical in
/-- **If `χ_n(σ) ≠ 1` then `det (ρ_{E,n}(σ)) ≠ 1`**, for the matrix representation at any basis.

⚠️ It produces no such `σ`, and this development has one at `n = 3` only
(`exists_galoisModularCyclotomicChar_three_ne_one`, `#947`); the non-vacuity block fires it
there. -/
theorem det_galoisRepModMatrix_n_ne_one_of_galoisModularCyclotomicChar_ne_one {n : ℕ} [NeZero n]
    (b : Module.Basis (Fin 2) (ZMod n) ((W⁄F).torsion n)) {σ : F ≃ₐ[S] F} (h2 : (2 : F) ≠ 0)
    (hn : ((n : ℤ) : F) ≠ 0)
    (hσ : galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_intCast_ne_zero hn) σ ≠ 1) :
    Matrix.GeneralLinearGroup.det (galoisRepModMatrix b σ) ≠ 1 := by
  rw [det_galoisRepModMatrix_n_eq_galoisModularCyclotomicChar b h2 hn]
  exact hσ

open Classical in
/-- **The image of `ρ_{E,n}` is not contained in `SL₂(ℤ/n)`**, as soon as one `σ` has `χ_n(σ) ≠ 1`
— and at **every** basis `b`, since `hσ` mentions none.

The inclusion is written as `(galoisRepModMatrix b).range ≤ (Matrix.SpecialLinearGroup.toGL).range`
with Mathlib's monoid embedding `SLₙ(R) →* GLₙ(R)`, so the statement is literally *"every matrix in
the image has determinant `1`"* negated.

⚠️ **This is the sentence the composition was worth stating for.**  It is about the matrix
representation and about a subgroup of matrices, and neither half on its own can say it: the
`TateModule/` side has no `χ_n`, and the `FunctionField/` side has no matrix. -/
theorem range_galoisRepModMatrix_n_not_le_range_toGL {n : ℕ} [NeZero n]
    (b : Module.Basis (Fin 2) (ZMod n) ((W⁄F).torsion n)) {σ : F ≃ₐ[S] F} (h2 : (2 : F) ≠ 0)
    (hn : ((n : ℤ) : F) ≠ 0)
    (hσ : galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_intCast_ne_zero hn) σ ≠ 1) :
    ¬ (galoisRepModMatrix b).range ≤
      (SpecialLinearGroup.toGL (n := Fin 2) (R := ZMod n)).range := by
  intro hle
  obtain ⟨A, hA⟩ := hle ⟨σ, rfl⟩
  refine det_galoisRepModMatrix_n_ne_one_of_galoisModularCyclotomicChar_ne_one b h2 hn hσ ?_
  rw [← hA]
  ext
  simp [SpecialLinearGroup.toGL]

end Galois


/-! ### Subsumption

⚠️ Compiled, not asserted.  The `example` below restates `#1243`'s headline
`det_comp_galoisRepModMatrix_three_eq_galoisModularCyclotomicChar` **binder for binder** —
including its own naming of the character through `natCard_rootsOfUnity_of_ne_zero h3` rather than
this file's `natCard_rootsOfUnity_of_intCast_ne_zero` — and proves it from the general layer.  The
two namings are interchangeable because the count is a `Prop` and `galoisModularCyclotomicChar`
takes it as a proof argument, so proof irrelevance makes the two characters the same term. -/

section Subsumption

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S} [W.IsElliptic]
  [IsAlgClosed F]

open Classical in
/-- `det_comp_galoisRepModMatrix_three_eq_galoisModularCyclotomicChar`, restated verbatim and
proved from the general layer. -/
example (b : Module.Basis (Fin 2) (ZMod 3) ((W⁄F).torsion 3)) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) :
    (Matrix.GeneralLinearGroup.det : GL (Fin 2) (ZMod 3) →* (ZMod 3)ˣ).comp
        (galoisRepModMatrix b)
      = galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_ne_zero h3) :=
  det_comp_galoisRepModMatrix_n_eq_galoisModularCyclotomicChar b h2 (by exact_mod_cast h3)

end Subsumption

/-! ### Non-vacuity

The curve is this front's standard certificate curve, `y² + y = x³` over `ℚ` base-changed to
`AlgebraicClosure ℚ`, with **`S = ℚ` and not `S = F`** — over `S = F` the group `Gal(F/S)` is
trivial and a certificate for a Galois *representation* says nothing.  This block declares no
fixture of its own (`#1408`).

⚠️ **The two indices certify different things and neither certifies both**, exactly as in
`EllipticCurves.FunctionField.WeilPairingDeterminantCharacterN`:

* **`n = 5` prices the index.**  `5` is not `3`-smooth, so `#1243`'s statements cannot be quoted at
  it at any hypotheses.  ⚠️ **Nothing there certifies that either side is non-trivial**: `χ_5` of
  `ℚ` being a non-trivial character is a statement about `AlgebraicClosure ℚ`, and nothing on `main`
  proves it.
* **`n = 3` prices the conclusion, and the mathematics there is `#1243`'s.**  The last certificate
  is its load-bearing one, re-derived through `range_galoisRepModMatrix_n_not_le_range_toGL`
  instead of through its `n = 3` twin.  ⚠️ It is stated for exactly that reason and is **not**
  evidence that this file proves anything new at `n = 3`.

⚠️ **The load-bearing certificate was tested by deleting its last named lemma** (`#944`).  Deleting
the `exact fun c => range_galoisRepModMatrix_n_not_le_range_toGL …` line, leaving the rest of the
script untouched, gives

```
error: unsolved goals
σ : Gal(AlgebraicClosure ℚ/ℚ)
hσ : (galoisModularCyclotomicChar ℚ (AlgebraicClosure ℚ) ⋯) σ ≠ 1
⊢ ∀ (c : Module.Basis (Fin 2) (ZMod 3) ↥(((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3)),
    ¬(galoisRepModMatrix c).range ≤ SpecialLinearGroup.toGL.range
```

⚠️ **Read the hypothesis list, not the error tag**: what survives is a statement about `χ_3` and a
goal about matrices, with *nothing relating them*.  The certificate is closed by this file's
identity and by nothing else. -/

section Nonvacuity

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

/-- The index condition `((n : ℤ) : F) ≠ 0` at `n = 3` over a field of characteristic `0`. -/
private lemma exampleIndexThree : (((3 : ℕ) : ℤ) : AlgClosedQ) ≠ 0 := by
  have h : (((3 : ℕ) : ℤ) : AlgClosedQ) = 3 := by push_cast; ring
  rw [h]; norm_num

/-- The same at `n = 5`, which is **not** `3`-smooth. -/
private lemma exampleIndexFive : (((5 : ℕ) : ℤ) : AlgClosedQ) ≠ 0 := by
  have h : (((5 : ℕ) : ℤ) : AlgClosedQ) = 5 := by push_cast; ring
  rw [h]; norm_num

open Classical in
/-- **⚠️ THE CERTIFICATE THAT PRICES THE INDEX**: the choice-free form on a curve that exists, at
`n = 5` — a basis, a matrix representation computing the Galois action, and `det = χ_5`, all
produced.  Unconditional, and `1 < 5` is bound nowhere in reaching it. -/
example : ∃ (c : Module.Basis (Fin 2) (ZMod 5) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 5))
      (ρ : (AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) →* GL (Fin 2) (ZMod 5)),
      (∀ (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) (P : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 5),
        ⇑(c.repr (σ • P)) = (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod 5)) *ᵥ ⇑(c.repr P)) ∧
      ∀ σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ, Matrix.GeneralLinearGroup.det (ρ σ)
        = galoisModularCyclotomicChar ℚ AlgClosedQ
            (natCard_rootsOfUnity_of_intCast_ne_zero (F := AlgClosedQ) (n := 5)
              exampleIndexFive) σ :=
  exists_galoisRepModMatrix_n_det_eq_galoisModularCyclotomicChar exampleTwo exampleIndexFive

open Classical in
/-- The pointwise identity on the same curve, at an **arbitrary** basis and an arbitrary `σ`, so
that the certificate above is not read as being about the one basis it produces. -/
example (b : Module.Basis (Fin 2) (ZMod 5) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 5))
    (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) :
    Matrix.GeneralLinearGroup.det (galoisRepModMatrix b σ)
      = galoisModularCyclotomicChar ℚ AlgClosedQ
          (natCard_rootsOfUnity_of_intCast_ne_zero (F := AlgClosedQ) (n := 5)
            exampleIndexFive) σ :=
  det_galoisRepModMatrix_n_eq_galoisModularCyclotomicChar
    (W := y2AddYEqX3 ℚ) b exampleTwo exampleIndexFive σ

open Classical in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on `y² + y = x³` over `ℚ`, the image of the mod-`3` matrix
representation `Gal(ℚ̄/ℚ) →* GL₂(ℤ/3)` is **not** contained in `SL₂(ℤ/3)` — at every `ZMod 3`-basis
of `E[3]`, unconditionally.

⚠️ **It is `#1243`'s certificate and not a new theorem**; what is new is that it is closed through
the general layer.  See the block docstring. -/
example : ∀ c : Module.Basis (Fin 2) (ZMod 3) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3),
    ¬ (galoisRepModMatrix (S := ℚ) c).range
      ≤ (SpecialLinearGroup.toGL (n := Fin 2) (R := ZMod 3)).range := by
  obtain ⟨σ, hσ⟩ := exists_galoisModularCyclotomicChar_three_ne_one
    (natCard_rootsOfUnity_of_intCast_ne_zero (F := AlgClosedQ) (n := 3) exampleIndexThree)
  exact fun c => range_galoisRepModMatrix_n_not_le_range_toGL
    (W := y2AddYEqX3 ℚ) c exampleTwo exampleIndexThree hσ

end Nonvacuity

end WeierstrassCurve.Affine
