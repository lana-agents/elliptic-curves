/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.TateModule.MatrixRepThree
import EllipticCurves.TateModule.PrimaryMatrixRepCompat

/-!
# The two routes from a basis of `T₃E` to `GL₂(ℤ₃)` agree

`EllipticCurves.TateModule.MatrixRepThree` builds the matrix form of the `3`-adic Galois
representation by way of `matrixAutEquivThree`, the multiplicative equivalence

```
GL (Fin 2) ℤ_[3] ≃* Aut_{ℤ_[3]}(T₃E)
```

assembled from `Matrix.GeneralLinearGroup.toLin'` and
`LinearMap.GeneralLinearGroup.generalLinearEquiv`.
`EllipticCurves.TateModule.GeneralLinearGroup` builds the same identification for an arbitrary
free module over an arbitrary commutative ring, as `Module.Basis.linearEquivMulEquivGL`, but along
the other chain, through `LinearMap.toMatrixAlgEquiv`. This file records that at `ℓ = 3` the two
agree, and transports the entry formulas — including the one for the *inverse* matrix, which
`MatrixRepThree` does not supply.

⚠️ **This is not a second proof that the two chains agree; it is a second *spelling*.** The
agreement holds at every prime, over every commutative ring and for every basis — that is
`Module.Basis.linearEquivMulEquivGL_symm`. What is new here is that it is available under the
`Three` names, so a reader arriving from `EllipticCurves.TateModule.MatrixRepThree` finds it where
the `ℓ = 2` reader finds it.

## What this file contains, and what it does not

**Every argument is elsewhere and this file contains none.** The identity of the two chains is
`Module.Basis.linearEquivMulEquivGL_symm` (`EllipticCurves.TateModule.GeneralLinearGroup`), stated
for an arbitrary basis of an arbitrary module over an arbitrary commutative ring; its transport to
the Tate module is `EllipticCurves.TateModule.PrimaryMatrixRepCompat`, stated at an arbitrary
prime. **This file supplies the prime `ℓ = 3` and every proof below is one line.**

⚠️ **This file takes no hypothesis at all** — no `h2`, no `h3`, no `[IsAlgClosed F]`, no
`[(W'⁄F).IsElliptic]`. That is unlike every other `…Three` file on this front, and the reason is
structural rather than a strengthening: the basis `b` is an explicit argument here, so nothing
below needs `T₃E ≅ ℤ₃²`, which is where `h2` and `h3` enter everywhere else
(`EllipticCurves.TateModule.FreeThree`). ⚠️ **The price is that these statements say nothing until
a basis is produced**, and producing one at `ℓ = 3` does need both; see the `Nonvacuity` section,
which is where `h2` and `h3` appear.

## Naming, and the one declaration that has no twin here

The `ℓ = 3` names are the generic names with `Three` in place of the prime, matching
`EllipticCurves.TateModule.MatrixRepThree`'s spellings for the objects they are about.

⚠️ There is deliberately **no `linearEquivMulEquivGL_eq_three`.** Its `ℓ = 2` form,
`WeierstrassCurve.Affine.linearEquivMulEquivGL_eq`, carries no prime in its name, so it was
generalised in place in `EllipticCurves.TateModule.PrimaryMatrixRepCompat` rather than twinned;
applied to a basis of `T₃E` that generic statement already **is** the `ℓ = 3` statement. A twin of
an already-generic declaration is the duplication `EllipticCurves.TateModule.FreeThree` warns
about by name.

## Main statements

* `WeierstrassCurve.Affine.matrixAutEquivThree_eq` :
  `matrixAutEquivThree b = b.linearEquivMulEquivGL.symm`.
* `WeierstrassCurve.Affine.galoisRepMatrixThree_eq` :
  `ρ_{E,3}(σ) = b.linearEquivMulEquivGL (galoisRep 3 σ)`, the same representation read along the
  general chain.
* `WeierstrassCurve.Affine.coe_galoisRepMatrixThree_inv_apply` : the entries of `ρ_{E,3}(σ)⁻¹`.

## Scope

* **Nothing here strengthens what `MatrixRepThree` claims.** Continuity of `ρ_{E,3}` is not
  asserted here; it is `continuous_galoisRepMatrixThree`
  (`EllipticCurves.TateModule.MatrixContinuityThree`).
* ⚠️ **This does not unblock `det ρ_{E,3} = χ_3` `3`-adically**, and an entry formula for
  `ρ_{E,3}(σ)⁻¹` may look like progress towards it. The `3`-adic identity needs the Weil pairing on
  `E[3^k]` for **every** `k`. ⚠️ That is **not** the `ωₙ` crux, which is what this sentence used
  to name: `3 ^ k` is `3`-smooth at every `k`, and the rung-5 root and the rung-6 translation
  slot hold at every `3`-smooth `n` with no `y`-coordinate division polynomial anywhere
  (`#1165`, `#1304`, `#1308`). What is missing up the tower is `hprin`, produced only at
  `n = 2` and `n = 3` (`exists_gS_{two,three}_of_isAlgClosed`). The **mod-`3`** identity is a
  different statement about a different object and is
  `EllipticCurves.FunctionField.WeilPairingDeterminantCharacter`.
* ⚠️ **Injectivity, surjectivity and openness of `ρ_{E,3}` all stay out.** An entry-by-entry
  agreement of two constructions of the same homomorphism says nothing about any of them.
* `ℓ ≥ 5` gains nothing from this file. The generic statements it instantiates already hold at
  every prime — what is missing there is a basis of `T_ℓE`, which needs `#E[ℓ^k]` and surjectivity
  of `[ℓ]` on `E(F̄)`, i.e. the multiplication-by-`n` coordinate formula `x(nP) = Φₙ/ΨSqₙ`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7 and VII.7.
-/

open Matrix

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
variable (b : Module.Basis (Fin 2) ℤ_[3] ((W'⁄F).tateModule 3))

/-- **The two identifications of `Aut_{ℤ_[3]}(T₃E)` with `GL₂(ℤ_[3])` agree.**

`matrixAutEquivThree b` goes `GL → Aut` through `Matrix.GeneralLinearGroup.toLin'`, while
`b.linearEquivMulEquivGL` goes `Aut → GL` through `LinearMap.toMatrixAlgEquiv`. Both send a matrix
`M` to the endomorphism `v ↦ ∑ i, (M *ᵥ b.repr v) i • b i`, so they are mutually inverse.
Definitionally `matrixAutEquiv_eq` at `ℓ = 3`. -/
theorem matrixAutEquivThree_eq : matrixAutEquivThree b = b.linearEquivMulEquivGL.symm :=
  matrixAutEquiv_eq b

/-- **`ρ_{E,3}` read along the general chain.** `galoisRepMatrixThree` is `galoisRep 3` pushed
through `Module.Basis.linearEquivMulEquivGL`, so every lemma about the latter applies to it. -/
theorem galoisRepMatrixThree_eq (σ : F ≃ₐ[S] F) :
    galoisRepMatrixThree b σ = b.linearEquivMulEquivGL (galoisRep 3 σ) :=
  galoisRepMatrix_eq b σ

/-- The entries of `ρ_{E,3}(σ)`, re-derived from the general entry formula. This is
`galoisRepMatrixThree_apply_coe`; it is restated here to confirm that the two chains produce the
same matrix entry-by-entry, and not merely the same abstract group element. -/
theorem coe_galoisRepMatrixThree_apply' (σ : F ≃ₐ[S] F) (i j : Fin 2) :
    (galoisRepMatrixThree b σ : Matrix (Fin 2) (Fin 2) ℤ_[3]) i j = b.repr (σ • b j) i :=
  coe_galoisRepMatrix_apply' b σ i j

/-- **The entries of `ρ_{E,3}(σ)⁻¹`.** Column `j` records the coordinates of `σ⁻¹ • b j`, since
`ρ_{E,3}` is a homomorphism from a group. `MatrixRepThree` supplies no formula for the inverse
matrix; this one comes for free from `Module.Basis.coe_inv_linearEquivMulEquivGL_apply`. -/
theorem coe_galoisRepMatrixThree_inv_apply (σ : F ≃ₐ[S] F) (i j : Fin 2) :
    (((galoisRepMatrixThree b σ)⁻¹ : GL (Fin 2) ℤ_[3]) : Matrix (Fin 2) (Fin 2) ℤ_[3]) i j
      = b.repr (σ⁻¹ • b j) i :=
  coe_galoisRepMatrix_inv_apply b σ i j

/-! ### Non-vacuity

⚠️ The statements above are **equations, not existentials**, so the usual "witnessed by something
trivial" reading is not the risk. The risk is the other one: every one of them is universally
quantified over a basis of `T₃E`, so if no such basis existed on any curve they would all be
vacuously true and this file would assert nothing.

What is certified below, on `y² + y = x³` over `ℚ` base-changed to an algebraic closure of `ℚ` with
**`S = ℚ`** so that `Gal(F/S)` is not the trivial group — this front's standard `n = 3` certificate
curve:

1. a basis of `T₃E` genuinely exists there, and one of the entry formulas above holds for it,
   stated in full and closed **by application** rather than by `rfl`, `decide` or `norm_num`;
2. the module the matrices act on is not the zero module, by a route that never mentions matrices.

⚠️ Without half 2 the certificate would be worthless: over a zero module `b.repr` is constantly `0`
and every entry formula reads `0 = 0`.

⚠️ **`Algebra.IsIntegral ℚ (AlgebraicClosure ℚ)` is not needed here and no `exampleIsIntegral`
workaround appears below.** That instance is the one
`EllipticCurves.TateModule.MatrixContinuityThree` has to introduce by hand, because instance
search picks `DivisionRing.toRatAlgebra` over
`AlgebraicClosure.instAlgebra ℚ` in an import closure this large. No statement in this file or in
`EllipticCurves.TateModule.PrimaryMatrixRepCompat` carries `[Algebra.IsIntegral S F]`, so the trap
cannot fire; copying the workaround would be cargo.
-/

section Nonvacuity

/-! The certificate curve `y² + y = x³` over `ℚ` and its base — algebraically closed so that
`Gal(F/ℚ)` is not the trivial group, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — are the
shared `EllipticCurves.Fixture.y2AddYEqX3` and `EllipticCurves.Fixture.AlgClosedQ`, which also
supply `(y2AddYEqX3 ℚ).IsElliptic` from a single `[CharZero F]` instance. The **base-changed**
`((y2AddYEqX3 ℚ)⁄AlgClosedQ).IsElliptic` comes from the same module, via
`EllipticCurves.Fixture.instIsEllipticBaseChange`; this block declares no fixture of its own
(`#1408`). -/

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

open Classical in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on a curve that exists, over a base field `S = ℚ` whose
absolute Galois group is not trivial, a basis of `T₃E` really does exist, and the two chains really
do produce the same matrix entry-by-entry for it — including for the inverse matrix, which is the
formula this file adds.

⚠️ The statement is restated in full rather than obtained-and-projected (`#916`), and the basis is
existentially quantified inside it rather than assumed, so nothing here is conditional on a basis
that might not be there. -/
example : ∃ b : Module.Basis (Fin 2) ℤ_[3] (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 3),
    ∀ (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) (i j : Fin 2),
      (((galoisRepMatrixThree b σ)⁻¹ : GL (Fin 2) ℤ_[3]) : Matrix (Fin 2) (Fin 2) ℤ_[3]) i j
        = b.repr (σ⁻¹ • b j) i :=
  (tateModule.nonempty_basis_tateModule_three (W := (y2AddYEqX3 ℚ)⁄AlgClosedQ) exampleTwo
    exampleThree).elim fun b => ⟨b, fun σ i j => coe_galoisRepMatrixThree_inv_apply b σ i j⟩

open Classical in
/-- **The module the matrices act on is not the zero module**, on the same curve, by a route that
never mentions the matrix representation: `T₃E` surjects onto `E[3^k]`, which has `9^k` elements.

⚠️ This is what rules out the degenerate reading of the certificate above: over a zero module every
coordinate would be `0` and every entry formula would read `0 = 0`. -/
example : Infinite (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 3) :=
  tateModule.infinite_tateModule_three exampleTwo exampleThree

end Nonvacuity

end WeierstrassCurve.Affine
