/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.TateModule.MatrixRepThree
import EllipticCurves.TateModule.PrimaryDeterminant

/-!
# The canonical invariants of `ρ_{E,3}` : determinant, trace, characteristic polynomial

For a Weierstrass curve `W'` over a field `S`, an algebraically closed extension `F / S` with
`(2 : F) ≠ 0` and `(3 : F) ≠ 0` for which `W'⁄F` is elliptic, and `G = F ≃ₐ[S] F`, this file
states the two canonical invariants of the `3`-adic Galois representation,

```
galoisDetThree   : G →* ℤ_[3]ˣ        the determinant character  det ρ_{E,3}
galoisTraceThree : G → ℤ_[3]          the trace                  tr  ρ_{E,3}
```

together with the statements that every basis of `T₃E` computes them, the resulting
basis-independence corollaries, and the characteristic polynomial `X² - (tr) X + (det)`.

This is the **second** prime at which the `ℓ`-adic invariants are available in this development,
and the first odd one.

## What this file contains, and what it does not

The invariants are in `EllipticCurves.TateModule.PrimaryDeterminant`, stated for an arbitrary prime
`ℓ`. **This file supplies its one input at `ℓ = 3` and contains no argument**: every proof below is
one line. The input is `nonempty_tateModuleEquivProd_three`
(`EllipticCurves.TateModule.FreeThree`, `#974`), and it is needed only by the two non-degeneracy
statements — the definitions, the computation rules and the basis-independence corollaries need
nothing at all.

⚠️ **That asymmetry is the thing to know before pricing anything downstream of this file.**
`galoisDetThree`, `galoisTraceThree`, `galoisDetThree_apply` and `galoisDetThree_one` were
stateable before `EllipticCurves.TateModule.MatrixRepThree` existed, because `LinearEquiv.det` and
`LinearMap.trace` are total and `galoisRep ℓ` was already `ℓ`-generic. `galoisTraceThree_one`
needed `#974` and nothing else. Only the every-basis-computes-them half and its corollaries needed
the matrix representation.

⚠️ **Two hypotheses, not one.** Where the `ℓ = 2` file `EllipticCurves.TateModule.Determinant`
carries only `h2`, the non-degeneracy statements here carry both `h2` and `h3`, and the provenance
is not symmetric: `nsmul_three_surjective` needs **only** `(2 : F) ≠ 0`, so the coherent system's
*lifting* step is `h3`-free; `h3` enters exclusively through the counting theorem
`card_torsion_three_pow`, i.e. through `#E[3] = 9`. `EllipticCurves.TateModule.FreeThree`
documents that split and this file inherits it unchanged rather than re-deriving it.

## Naming, and why there are `Three` twins of generic definitions here

⚠️ The rule `EllipticCurves.TateModule.MatrixRepThree` records applies verbatim: a twin of an
already-generic definition is normally pure duplication, and the two definitions below are the same
deliberate exception. Their `ℓ = 2` twins `galoisDetTwo` and `galoisTraceTwo` predate the
extraction and cannot be removed, and leaving `ℓ = 3` without the matching spellings would put the
two primes on different footings for every downstream file that extends by pattern.

Each `Three` definition is *definitionally* its generic form, so a consumer may use either spelling
and the generic lemmas apply to both.

## Non-degeneracy

⚠️ **This is the one place on this front where vacuity is not a formality, and the `ℓ = 2` file
says so first.** `LinearMap.det` is `1` and `LinearMap.trace` is `0` on modules that are not free
and finite, so `galoisDetThree` and `galoisTraceThree` are definable **with no hypotheses
whatsoever** and every identity between them would hold for the zero module. The statement that
rules that out is `galoisTraceThree_one : galoisTraceThree 1 = 2`, which is `2` exactly because
`Module.finrank ℤ_[3] T₃E = 2` and would be `0` for the zero module.

The `Nonvacuity` section at the end additionally exhibits a curve on which the hypotheses hold, and
— by a route that never mentions determinants — that `T₃E` is infinite, since a `GL₂`-shaped
statement about a zero module is satisfiable by anything.

## Scope

* ⚠️ **This file consumes the multiplication-by-`n` coordinate formula `x(nP) = Φₙ/ΨSqₙ`**, at
  `n = 3`, through `EllipticCurves.Torsion.TriplingSurjective` and hence through
  `EllipticCurves.TateModule.FreeThree`. `EllipticCurves.TateModule.Determinant` says of the
  `ℓ = 2` route that it needs no such thing; **that sentence must not be read as applying here.**
* ⚠️ **`det ρ_{E,3} = χ_3` `3`-adically is NOT unblocked by this file**, and this file will look as
  though it just got closer. The `3`-adic identity needs the Weil pairing on `E[3^k]` for **every**
  `k`, i.e. the pairing at composite `n`, exactly as at `ℓ = 2`; this development has the pairing at
  `n = 2` and `n = 3` only. The **mod-`3`** identity `galoisDetMod 3 = χ_3` is a *different
  statement about a different object* — `galoisDetMod 3` is valued in `(ZMod 3)ˣ`, not `ℤ_[3]ˣ` —
  and it landed separately as
  `EllipticCurves.FunctionField.WeilPairingDeterminantCharacter` (`#958`).
  `EllipticCurves.TateModule.Determinant`'s Scope makes this distinction carefully for `ℓ = 2`;
  it is repeated rather than re-invented here.
* **Continuity is not asserted here**, and it is no longer missing at `ℓ = 3`:
  `continuous_galoisDetThree` and `continuous_galoisTraceThree` are in
  `EllipticCurves.TateModule.MatrixContinuityThree`, over the `ℓ`-generic
  `EllipticCurves.TateModule.PrimaryMatrixContinuity`, and they take the same `h2` and `h3` the
  `Non-degeneracy` section below takes. ⚠️ **The clause this bullet used to carry is false** —
  *"their `ℓ = 3` twins are a separate follow-up, and they are what makes that file's `ℓ = 3` twin
  a real piece of work rather than an instantiation"*: the follow-up has landed, and the twin is
  seven one-line instantiations, not eighteen restatements.
* **The basis-change conjugation law is not here.** ⚠️ The clause this bullet used to carry —
  *"`galoisRepMatrixTwo_conj` (`EllipticCurves.TateModule.MatrixRepBasisChange`) is likewise still
  `ℓ = 2` only. Its statement is insensitive to `ℓ`, so it is a mechanical follow-up that nothing
  blocks"* — was a correct prediction and has been paid: the law is stated at an arbitrary prime in
  `EllipticCurves.TateModule.PrimaryMatrixRepBasisChange` and at `ℓ = 3` in
  `EllipticCurves.TateModule.MatrixRepBasisChangeThree`. Neither file consumes this one; the
  conjugation law does not touch the determinant.
* **The image is not here**, and it is no longer missing at `ℓ = 3` either:
  `isClosed_range_galoisDetThree` is in `EllipticCurves.TateModule.ImageThree`, over the
  `ℓ`-generic `EllipticCurves.TateModule.PrimaryImage`. ⚠️ **Two successive clauses of this bullet
  have gone false and both are recorded rather than deleted.** The first read *"because their input
  `continuous_galoisRepMatrixTwo` is"*, which expired when
  `EllipticCurves.TateModule.MatrixContinuityThree` landed; the second read *"nothing gates their
  `ℓ = 3` layer; it has simply not been written"*, and it has now been written. ⚠️ **A third
  clause has since gone false in its turn** — it read *"what remains true of exactly one of the two
  files: `EllipticCurves.TateModule.ImageProfinite` is still `ℓ = 2` only, ungated, and a separate
  follow-up"*. That follow-up is `EllipticCurves.TateModule.ImageProfiniteThree`, over the
  `ℓ`-generic `EllipticCurves.TateModule.PrimaryImageProfinite`.
* **General odd `ℓ ≥ 5` stays out.** `EllipticCurves.TateModule.PrimaryDeterminant` is already
  stated at an arbitrary prime, so the `ℓ = 5` file will again be a list of instantiations — but
  its input `Nonempty (T₅E ≃ₗ ℤ_[5]²)` is gated on `#E[5^k]`.  ⚠️ This bullet used to say it was
  gated *"on `[5]`-surjectivity and `#E[5^k]`, both of which need the general coordinate formula,
  i.e. the `ωₙ` crux"*, and all three clauses are wrong: `[5]`-surjectivity holds at every nonzero
  index (`nsmul_surjective_of_two_ne_zero`, `EllipticCurves.Torsion.TwoTorsionOrder`); the
  coordinate formula is proved at every index (`hasXCoordFormula_of_two_ne_zero`,
  `EllipticCurves.Torsion.NsmulOrder`); and it is **not** the `ωₙ` crux, which is `#404`'s on-curve
  identity, closed in `EllipticCurves.Torsion.OmegaCrux` (PR #557).
  ⚠️ **`#E[ℓ^k]` is not open at any prime `ℓ` with `(ℓ : F) ≠ 0`, and this file's generic sibling
  is now instantiated there.** The sharp count is `card_torsion_eq_sq`
  (`EllipticCurves.Torsion.StructureGeneral`, `#293`): every `n` with `(n : F) ≠ 0`, `ℓ = 2`
  included, so it is sharper than the odd-`ℓ` attribution this bullet used to carry.
  `nonempty_tateModuleEquivProd_of_natCast_ne_zero` (`EllipticCurves.TateModule.FreeGeneral`,
  `#268`) turns that count into the rank-two input the generic layer takes as an argument, and
  **`EllipticCurves.TateModule.DeterminantGeneral` supplies it at every prime `ℓ` with
  `(ℓ : F) ≠ 0`** — so *"separate work and is not done here"* is discharged rather than owed. ⚠️
  `(ℓ : F) ≠ 0` is sharp: at `ℓ = char F` the conclusion is **false**, not open — `E[ℓ]` is `0` or
  `ℤ/ℓℤ`, so `T_ℓE` has rank `0` or `1`.

## Main definitions

* `WeierstrassCurve.Affine.galoisDetThree` : the determinant character `G →* ℤ_[3]ˣ`.
* `WeierstrassCurve.Affine.galoisTraceThree` : the trace `G → ℤ_[3]`.

## Main statements

* `WeierstrassCurve.Affine.coe_galoisDetThree`,
  `WeierstrassCurve.Affine.trace_galoisRepMatrixThree` : every basis computes the invariants.
* `WeierstrassCurve.Affine.det_galoisRepMatrixThree_congr`,
  `WeierstrassCurve.Affine.trace_galoisRepMatrixThree_congr`,
  `WeierstrassCurve.Affine.charpoly_galoisRepMatrixThree_congr` : independence of the basis.
* `WeierstrassCurve.Affine.charpoly_galoisRepMatrixThree` : `X² - (tr) X + (det)`.
* `WeierstrassCurve.Affine.galoisTraceThree_one` : `tr ρ(1) = 2`, the rank-two non-degeneracy
  witness.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7 and III.8.1.
-/

open Matrix Polynomial

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}

/-! ### The invariants -/

/-- **The determinant character of the `3`-adic representation**, `det ρ_{E,3} : G →* ℤ_[3]ˣ`.
Definitionally `galoisDet` at `ℓ = 3`.

⚠️ This needs no hypothesis and never did: `LinearEquiv.det` is total and `galoisRep 3` was already
available. It is `galoisTraceThree_one` that makes the definition worth having. -/
noncomputable def galoisDetThree : (F ≃ₐ[S] F) →* ℤ_[3]ˣ :=
  galoisDet (W' := W') (F := F) (ℓ := 3)

/-- **The trace of the `3`-adic representation**, `tr ρ_{E,3} : G → ℤ_[3]`. Definitionally
`galoisTrace` at `ℓ = 3`. Not a monoid homomorphism, since the trace is not multiplicative. -/
noncomputable def galoisTraceThree (σ : F ≃ₐ[S] F) : ℤ_[3] :=
  galoisTrace (W' := W') (F := F) (ℓ := 3) σ

theorem galoisDetThree_apply (σ : F ≃ₐ[S] F) :
    galoisDetThree (W' := W') (F := F) σ
      = LinearEquiv.det (M := (W'⁄F).tateModule 3) (galoisRep 3 σ) :=
  galoisDet_apply σ

/-- The determinant character is trivial at the identity. ⚠️ Like `galoisDetThree` itself this
holds for the zero module, so it is **not** a non-degeneracy witness; `galoisTraceThree_one` is. -/
@[simp]
theorem galoisDetThree_one : galoisDetThree (W' := W') (F := F) 1 = 1 := galoisDet_one

/-! ### Every basis computes the invariants -/

variable (b b' : Module.Basis (Fin 2) ℤ_[3] ((W'⁄F).tateModule 3))

/-- **The matrix representation is Mathlib's `LinearMap.toMatrix` of the Galois action**, at
`ℓ = 3`. Everything else in this section follows from it. -/
theorem galoisRepMatrixThree_eq_toMatrix (σ : F ≃ₐ[S] F) :
    (galoisRepMatrixThree b σ : Matrix (Fin 2) (Fin 2) ℤ_[3])
      = LinearMap.toMatrix b b ((galoisRep 3 σ : (W'⁄F).tateModule 3 ≃ₗ[ℤ_[3]] _) :
          (W'⁄F).tateModule 3 →ₗ[ℤ_[3]] (W'⁄F).tateModule 3) :=
  galoisRepMatrix_eq_toMatrix b σ

/-- **The determinant of the matrix computes the determinant character**, for every basis `b`.

⚠️ This carries neither `[IsAlgClosed F]` nor `[(W'⁄F).IsElliptic]`, and the omission is measured
rather than hopeful: it is a statement about a basis you were *handed*, so it does not care where
the basis came from. `EllipticCurves.TateModule.Determinant`'s `coe_galoisDetTwo` is outside its
`Nondegenerate` section for the same reason. -/
theorem coe_galoisDetThree (σ : F ≃ₐ[S] F) :
    ((galoisDetThree (W' := W') (F := F) σ : ℤ_[3]ˣ) : ℤ_[3])
      = (galoisRepMatrixThree b σ : Matrix (Fin 2) (Fin 2) ℤ_[3]).det :=
  coe_galoisDet b σ

/-- **The trace of the matrix computes the trace of the representation**, for every basis `b`. -/
theorem trace_galoisRepMatrixThree (σ : F ≃ₐ[S] F) :
    (galoisRepMatrixThree b σ : Matrix (Fin 2) (Fin 2) ℤ_[3]).trace
      = galoisTraceThree (W' := W') (F := F) σ :=
  trace_galoisRepMatrix b σ

/-- **The characteristic polynomial of `ρ_{E,3}(σ)`**, in terms of the two canonical invariants.
Since the right-hand side does not mention `b`, neither does the characteristic polynomial. -/
theorem charpoly_galoisRepMatrixThree (σ : F ≃ₐ[S] F) :
    (galoisRepMatrixThree b σ : Matrix (Fin 2) (Fin 2) ℤ_[3]).charpoly
      = X ^ 2 - C (galoisTraceThree (W' := W') (F := F) σ) * X
        + C ((galoisDetThree (W' := W') (F := F) σ : ℤ_[3]ˣ) : ℤ_[3]) :=
  charpoly_galoisRepMatrix b σ

/-! ### Independence of the basis -/

/-- **`det ρ_{E,3}(σ)` does not depend on the basis.** -/
theorem det_galoisRepMatrixThree_congr (σ : F ≃ₐ[S] F) :
    (galoisRepMatrixThree b σ : Matrix (Fin 2) (Fin 2) ℤ_[3]).det
      = (galoisRepMatrixThree b' σ : Matrix (Fin 2) (Fin 2) ℤ_[3]).det :=
  det_galoisRepMatrix_congr b b' σ

/-- **`tr ρ_{E,3}(σ)` does not depend on the basis.** -/
theorem trace_galoisRepMatrixThree_congr (σ : F ≃ₐ[S] F) :
    (galoisRepMatrixThree b σ : Matrix (Fin 2) (Fin 2) ℤ_[3]).trace
      = (galoisRepMatrixThree b' σ : Matrix (Fin 2) (Fin 2) ℤ_[3]).trace :=
  trace_galoisRepMatrix_congr b b' σ

/-- **The characteristic polynomial of `ρ_{E,3}(σ)` does not depend on the basis.** -/
theorem charpoly_galoisRepMatrixThree_congr (σ : F ≃ₐ[S] F) :
    (galoisRepMatrixThree b σ : Matrix (Fin 2) (Fin 2) ℤ_[3]).charpoly
      = (galoisRepMatrixThree b' σ : Matrix (Fin 2) (Fin 2) ℤ_[3]).charpoly :=
  charpoly_galoisRepMatrix_congr b b' σ

/-! ### Computation rules -/

/-- The determinant character in coordinates: the `2 × 2` determinant of the matrix whose columns
are the coordinate vectors of the Galois translates of the basis vectors. -/
theorem coe_galoisDetThree_eq (σ : F ≃ₐ[S] F) :
    ((galoisDetThree (W' := W') (F := F) σ : ℤ_[3]ˣ) : ℤ_[3])
      = b.repr (σ • b 0) 0 * b.repr (σ • b 1) 1 - b.repr (σ • b 1) 0 * b.repr (σ • b 0) 1 :=
  coe_galoisDet_eq b σ

/-- The trace in coordinates. -/
theorem galoisTraceThree_eq (σ : F ≃ₐ[S] F) :
    galoisTraceThree (W' := W') (F := F) σ = b.repr (σ • b 0) 0 + b.repr (σ • b 1) 1 :=
  galoisTrace_eq b σ

/-- The determinant of `galoisRepMatrixThree b σ` is a unit — it is the value of a character with
values in `ℤ_[3]ˣ`. -/
theorem isUnit_det_galoisRepMatrixThree (σ : F ≃ₐ[S] F) :
    IsUnit (galoisRepMatrixThree b σ : Matrix (Fin 2) (Fin 2) ℤ_[3]).det :=
  isUnit_det_galoisRepMatrix b σ

/-! ### Non-degeneracy -/

section Nondegenerate

variable [IsAlgClosed F] [(W'⁄F).IsElliptic]

/-- **`tr ρ_{E,3}(1) = 2`.** The statement that pins down what the rest of the file is about: it is
`Module.finrank ℤ_[3] T₃E`, so it is `2` exactly because `T₃E` has rank two, and it would be `0` if
`T₃E` were the zero module — the degenerate case `LinearMap.trace` would otherwise silently allow.

⚠️ This is one of exactly **two** places in the file where `[IsAlgClosed F]`,
`[(W'⁄F).IsElliptic]`, `h2` and `h3` are used at all — the other is
`charpoly_galoisRepMatrixThree_one` below, which uses them identically. Both use them only to
produce `nonempty_tateModuleEquivProd_three h2 h3`, which is the single hypothesis of
`galoisTrace_one_of_nonempty`. Everything above holds for a basis you were handed.

⚠️ **Deletion test**, measured on this file as committed. Replacing the argument
`(nonempty_tateModuleEquivProd_three h2 h3)` by a hole — `by refine
galoisTrace_one_of_nonempty (W' := W') (F := F) (ℓ := 3) ?_` — leaves

```
error: unsolved goals
S : Type u_1
F : Type u_2
inst✝⁵ : Field S
inst✝⁴ : Field F
inst✝³ : DecidableEq F
inst✝² : Algebra S F
W' : Affine S
inst✝¹ : IsAlgClosed F
inst✝ : WeierstrassCurve.IsElliptic W'⁄F
h2 : 2 ≠ 0
h3 : 3 ≠ 0
⊢ Nonempty (↥((W'⁄F).tateModule 3) ≃ₗ[ℤ_[3]] ℤ_[3] × ℤ_[3])
```

⚠️ `h2` and `h3` both **survive** in the context, so what the deletion removes is a construction and
not a hypothesis, and the residual is a **goal**, which no type mismatch could produce. It is
`#974`'s theorem — the rank-two input, and the only thing at `ℓ = 3` that ever cost anything. -/
theorem galoisTraceThree_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    galoisTraceThree (W' := W') (F := F) 1 = 2 :=
  galoisTrace_one_of_nonempty (tateModule.nonempty_tateModuleEquivProd_three h2 h3)

/-- **The characteristic polynomial of the identity is `(X - 1)²`.** Written out as `X² - 2X + 1`,
this is `galoisTraceThree_one` and `galoisDetThree_one` combined, and is again a statement that
fails for the zero module. -/
theorem charpoly_galoisRepMatrixThree_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    (galoisRepMatrixThree b 1 : Matrix (Fin 2) (Fin 2) ℤ_[3]).charpoly
      = X ^ 2 - C 2 * X + C 1 :=
  charpoly_galoisRepMatrix_one_of_nonempty b
    (tateModule.nonempty_tateModuleEquivProd_three h2 h3)

end Nondegenerate

/-! ### Non-vacuity

⚠️ Everything in the `Non-degeneracy` section carries `[IsAlgClosed F]` and `[(W'⁄F).IsElliptic]`,
so `ℚ` cannot witness it and the statements would all be vacuously true if nothing inhabited those
classes. The block below rules that out on `y² + y = x³` base-changed to `AlgebraicClosure ℚ`, this
front's standard `n = 3` certificate curve, with **`S = ℚ`** so that `Gal(F/S)` is not trivial —
the same curve `EllipticCurves.TateModule.FreeThree` and `EllipticCurves.TateModule.MatrixRepThree`
use. ⚠️ All three now name the one shared fixture `EllipticCurves.Fixture.y2AddYEqX3` rather than
each carrying a `private` copy of it.

⚠️ **`open Classical in` is load-bearing on both certificates below, and it is not optional here.**
The `TateModule` family carries `[DecidableEq F]` in its `variable` blocks, but `AlgClosedQ` is
`AlgebraicClosure ℚ`, which has no decidable equality, so the section variable cannot supply one
and the block does not elaborate without it. `EllipticCurves.TateModule.MatrixRepThree` and
`EllipticCurves.TateModule.FreeThree` do the same; this note is here because the failure mode is a
`failed to synthesize instance of type class DecidableEq AlgClosedQ` at the `example`, several
lines away from the `AlgClosedQ` fixture that causes it.

⚠️ **Two certificates, closing two different risks**, following the idiom
`EllipticCurves.TateModule.MatrixRepThree` introduced: the first exhibits a curve on which
`galoisTraceThree 1 = 2` holds, and the second says `T₃E` is infinite by a route that never
mentions determinants. Without the second, `tr ρ(1) = 2` would still be the *interesting*
statement — it is `0` for the zero module — but the reader would have to take the file's word that
the module is not degenerate rather than see it.
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
absolute Galois group is not trivial, the trace of `ρ_{E,3}` at the identity really is `2`.

⚠️ It closes by **application** of `galoisTraceThree_one`, not by `rfl`, `decide` or `norm_num`, so
it consumes the theorem it certifies (`#944`). -/
example : galoisTraceThree (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) 1 = 2 :=
  galoisTraceThree_one exampleTwo exampleThree

open Classical in
/-- **The module the invariants are invariants of is not the zero module**, on the same curve, by a
route that never mentions the determinant or the trace: `T₃E` surjects onto `E[3^k]`, which has
`9^k` elements.

⚠️ This is what rules out the degenerate reading that the `Non-degeneracy` section warns about.
`galoisDetThree` and `galoisTraceThree` are definable over a zero module and every identity between
them holds there; `galoisTraceThree_one` is what fails there, and this is the independent check
that the module in question is genuinely infinite. -/
example : Infinite (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 3) :=
  tateModule.infinite_tateModule_three exampleTwo exampleThree

end Nonvacuity

end WeierstrassCurve.Affine
