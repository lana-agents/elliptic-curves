/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.TateModule.DeterminantModGeneral
import EllipticCurves.TateModule.MatrixRepMod

/-!
# `ρ_{E,n} : G → GL₂(ℤ/nℤ)` at EVERY `n > 1` with `(n : F) ≠ 0`

`EllipticCurves.TateModule.MatrixRepMod` builds the mod-`n` matrix representation

```
∃ c ρ, (∀ σ P, c.repr (σ • P) = ρ σ *ᵥ c.repr P) ∧ ∀ σ, det (ρ σ) = galoisDetMod n σ
```

at every **`3`-smooth** `n > 1`.  This file removes the smoothness.  It contains **one theorem and
no argument**: `exists_galoisRepModMatrix_of_smooth`'s proof with `basisTorsionOfSmooth` replaced by
`basisTorsionOfNatCastNeZero` (`EllipticCurves.TateModule.DeterminantModGeneral`).

⚠️ **The smoothness never touched the representation.**  `galoisRepModMatrix` needs `[NeZero n]` and
nothing else, and `galoisRepModMatrix_mulVec` and `det_galoisRepModMatrix` are stated at an
arbitrary basis; `MatrixRepMod`'s own section header says so — *"`3`-smoothness enters through the
**basis** and not through the representation"*.  Widening the basis therefore widens the existence
statement with no work, and this file is the compiled form of that sentence.

## Why this is a new file

⚠️ Measured, not argued.  The general basis lives in
`EllipticCurves.TateModule.DeterminantModGeneral`, which is a leaf over
`EllipticCurves.Torsion.StructureGeneral`; putting this theorem in `MatrixRepMod` instead would cost
that file **+34 modules** (40 → 74) and `EllipticCurves.TateModule.DeterminantModSmooth` the same
**+34** (37 → 71).  As a leaf it costs **0** to both.  See `DeterminantModGeneral`'s module
docstring for the full measurement and for the `OpenKernelGeneral` / `FreeGeneral` /
`MatrixRepGeneral` precedent this follows.

## Main statements

* `WeierstrassCurve.Affine.exists_galoisRepModMatrix_of_natCast_ne_zero` — the mod-`n` matrix
  representation exists at every `n > 1` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`.

## What is NOT here

* **`n = 2` and `n = 3`.**  `exists_galoisRepModMatrix_two` and `exists_galoisRepModMatrix_three`
  stay in `MatrixRepMod`.  The first is proved on `h2` alone from `card_torsion_two` and the general
  route would charge it a second cast hypothesis it does not need; the second rests on
  `basisTorsionThree`.  Neither is subsumed by anything below.
* **Deletions.**  `exists_galoisRepModMatrix_of_smooth` is kept.  It is an independent route for a
  consumer holding `hfac` and not carrying `EllipticCurves.Torsion.StructureGeneral` in its closure,
  which is the entire reason for the split; the `example` in the *Subsumption* block compiles the
  containment rather than asserting it.
* **The conjugation law, the kernel and the range.**  `galoisRepModMatrix_conj`,
  `ker_galoisRepModMatrix` and `range_galoisRepModMatrix_map` are stated in `MatrixRepMod` at an
  arbitrary basis and an arbitrary `[NeZero n]`.  They were never `3`-smooth and there is nothing to
  widen.
* **`det ρ_{E,n} = χ_n`.**  The determinant clause below identifies `det ∘ ρ` with `galoisDetMod n`,
  which is the basis-free character; identifying *that* with the cyclotomic character needs the Weil
  pairing and is `galoisDetMod_three_eq_galoisModularCyclotomicChar`, at `n = 3` only.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open Matrix

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}

/-! ### The choice-free existence statement -/

section Existence

variable [IsAlgClosed F] [(W'⁄F).IsElliptic] {n : ℕ} [NeZero n]

open Classical in
/-- **The mod-`n` matrix representation exists at every `n > 1` with `(n : F) ≠ 0`**, as a
representation that really does compute the Galois action and whose determinant is the basis-free
character `galoisDetMod n`.

The general-`n` mirror of `exists_galoisRepModMatrix_of_smooth`, and the same four-component
anonymous constructor: only the basis changed, from `basisTorsionOfSmooth` to
`basisTorsionOfNatCastNeZero`.

⚠️ `1 < n` is not bookkeeping and is inherited unchanged: it is what
`finrank_torsion_of_natCast_ne_zero` needs, and `EllipticCurves.TateModule.DeterminantModSmooth`
certifies that the rank is `1` and not `2` at `n = 1`, where `ZMod 1` is the trivial ring.

⚠️ `(n : F) ≠ 0` is sharp, not a relaxed smoothness: at `n = char F` the rank-two input is *false*,
so no basis indexed by `Fin 2` exists to build the representation on. -/
theorem exists_galoisRepModMatrix_of_natCast_ne_zero (h2 : (2 : F) ≠ 0) (hn1 : 1 < n)
    (hn : (n : F) ≠ 0) :
    ∃ (c : Module.Basis (Fin 2) (ZMod n) ((W'⁄F).torsion n))
      (ρ : (F ≃ₐ[S] F) →* GL (Fin 2) (ZMod n)),
      (∀ (σ : F ≃ₐ[S] F) (P : (W'⁄F).torsion n),
        ⇑(c.repr (σ • P)) = (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod n)) *ᵥ ⇑(c.repr P)) ∧
      ∀ σ : F ≃ₐ[S] F,
        Matrix.GeneralLinearGroup.det (ρ σ) = galoisDetMod (W' := W') (F := F) n σ :=
  ⟨basisTorsionOfNatCastNeZero (W := W'⁄F) h2 hn1 hn, galoisRepModMatrix _,
    galoisRepModMatrix_mulVec _, det_galoisRepModMatrix _⟩

end Existence

/-! ### Subsumption

⚠️ Compiled, not asserted, exactly as in `EllipticCurves.TateModule.DeterminantModGeneral`: the
`example` below restates `exists_galoisRepModMatrix_of_smooth` binder for binder and proves it from
the general layer, with `Nat.intCast_ne_zero_of_smooth`
(`EllipticCurves.Torsion.ThreePrimary`) as the bridge from `3`-smoothness to `(n : F) ≠ 0`. -/

section Subsumption

variable [IsAlgClosed F] [(W'⁄F).IsElliptic] {n : ℕ} [NeZero n]

open Classical in
/-- `exists_galoisRepModMatrix_of_smooth`, restated verbatim and proved from the general layer. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hn : 1 < n)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) :
    ∃ (c : Module.Basis (Fin 2) (ZMod n) ((W'⁄F).torsion n))
      (ρ : (F ≃ₐ[S] F) →* GL (Fin 2) (ZMod n)),
      (∀ (σ : F ≃ₐ[S] F) (P : (W'⁄F).torsion n),
        ⇑(c.repr (σ • P)) = (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod n)) *ᵥ ⇑(c.repr P)) ∧
      ∀ σ : F ≃ₐ[S] F,
        Matrix.GeneralLinearGroup.det (ρ σ) = galoisDetMod (W' := W') (F := F) n σ :=
  exists_galoisRepModMatrix_of_natCast_ne_zero h2 hn
    (by exact_mod_cast Nat.intCast_ne_zero_of_smooth h2 h3 (NeZero.ne n) hfac)

end Subsumption

/-! ### Non-vacuity

⚠️ **The index is `10`**, for the reason `EllipticCurves.TateModule.DeterminantModGeneral`'s
*Non-vacuity* block gives: `12` is `3`-smooth and a certificate there would be consistent with this
file proving nothing new, whereas `10 = 2 · 5` is **not** `3`-smooth — `Nat.ten_not_smooth`, and
that assertion is compiled in `DeterminantModGeneral` — so
`exists_galoisRepModMatrix_of_smooth` cannot state the certificate below at any hypotheses.

The curve is this front's standard one, `y² + y = x³` over `ℚ` base-changed to
`AlgebraicClosure ℚ`, with **`S = ℚ` and not `S = F`** — over `S = F` the group `Gal(F/S)` is
trivial and a certificate for a Galois *representation* says nothing.  This block declares no
fixture of its own (`#1408`). -/

section Nonvacuity

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleTen : ((10 : ℕ) : AlgClosedQ) ≠ 0 := by norm_num

open Classical in
/-- A `ZMod 10`-basis of `E[10]` on the certificate curve, fixed once so that the two certificates
below speak about the same representation. -/
private noncomputable def exampleBasis :
    Module.Basis (Fin 2) (ZMod 10) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 10) :=
  basisTorsionOfNatCastNeZero exampleTwo (by norm_num) exampleTen

open Classical in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on a curve that exists and at an index that is *not*
`3`-smooth, there really is a matrix representation `Gal(F/ℚ) →* GL₂(ℤ/10)` computing the Galois
action, whose determinant is `galoisDetMod 10`. -/
example : ∃ (c : Module.Basis (Fin 2) (ZMod 10) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 10))
      (ρ : (AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) →* GL (Fin 2) (ZMod 10)),
      (∀ (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) (P : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 10),
        ⇑(c.repr (σ • P)) = (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod 10)) *ᵥ ⇑(c.repr P)) ∧
      ∀ σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ,
        Matrix.GeneralLinearGroup.det (ρ σ)
          = galoisDetMod (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) 10 σ :=
  exists_galoisRepModMatrix_of_natCast_ne_zero exampleTwo (by norm_num) exampleTen

open Classical in
/-- The determinant bridge on the same curve at `n = 10`, written out at an arbitrary `σ` rather
than obtained-and-projected.  ⚠️ It consumes `det_galoisRepModMatrix`, which is stated in
`EllipticCurves.TateModule.MatrixRepMod` at an arbitrary basis and an arbitrary `[NeZero n]` — this
is the certificate that the *general* basis feeds it unchanged. -/
example (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) :
    Matrix.GeneralLinearGroup.det (galoisRepModMatrix exampleBasis σ)
      = galoisDetMod (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) 10 σ :=
  det_galoisRepModMatrix exampleBasis σ

open Classical in
/-- **⚠️ The conjugation law is not vacuous at `n = 10`** either: the conjugating element is not
always `1`, so `galoisRepModMatrix_conj` is not a disguised `b' = b`.  The witness is the reindexing
of `exampleBasis` along the transposition of the two indices, and
`basisChangeGL_reindex_swap_ne_one` (`EllipticCurves.TateModule.PrimaryMatrixRepBasisChange`) is
stated over an arbitrary `Nontrivial` commutative ring.  ⚠️ `Nontrivial (ZMod 10)` is where `1 < n`
shows up again: at `n = 1` the certificate would be false. -/
example : tateModule.basisChangeGL exampleBasis (exampleBasis.reindex (Equiv.swap 0 1)) ≠ 1 :=
  haveI : Fact (1 < 10) := ⟨by norm_num⟩
  tateModule.basisChangeGL_reindex_swap_ne_one exampleBasis

end Nonvacuity

end WeierstrassCurve.Affine
