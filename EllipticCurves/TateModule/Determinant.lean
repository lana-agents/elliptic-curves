/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.MatrixRep
import EllipticCurves.TateModule.PrimaryDeterminant

/-!
# The canonical invariants of `ρ_{E,2}` : determinant, trace, characteristic polynomial

`EllipticCurves.TateModule.MatrixRep` produces the `2`-adic Galois representation in matrix form,
`galoisRepMatrixTwo b : G →* GL₂(ℤ_[2])` for `G = F ≃ₐ[S] F`, but **only relative to a basis `b`**
of `T₂E`. There is no canonical basis: one comes from a coherent system of generating pairs of the
groups `E[2^k]`, and two systems give representations that differ by conjugation. So an individual
matrix entry of `galoisRepMatrixTwo b σ` carries no information about `E` — it is an artefact of
the choice.

This file extracts what survives the choice. The determinant and the trace of a `ℤ_[2]`-linear
endomorphism are defined basis-free in Mathlib (`LinearEquiv.det`, `LinearMap.trace`), so
composing them with `galoisRep 2` gives honest invariants of the curve and its Galois action:

```
galoisDetTwo   : G →* ℤ_[2]ˣ        the determinant character  det ρ_{E,2}
galoisTraceTwo : G → ℤ_[2]          the trace                  tr  ρ_{E,2}
```

and the theorems `coe_galoisDetTwo` and `trace_galoisRepMatrixTwo` say that for **every** basis
`b` the corresponding matrix quantity computes them. Their explicit corollaries
`det_galoisRepMatrixTwo_congr` and `trace_galoisRepMatrixTwo_congr` state the independence
directly: two bases, one answer.

Together the two determine the characteristic polynomial, which is therefore canonical as well:

```
charpoly_galoisRepMatrixTwo :
  (galoisRepMatrixTwo b σ).charpoly = X ^ 2 - C (galoisTraceTwo σ) * X + C (galoisDetTwo σ)
```

This is the shape in which the arithmetic eventually lives — for `S` a number field and `σ` a
Frobenius element the characteristic polynomial is `X² - a_p X + p`, with `galoisDetTwo` the
cyclotomic character and `galoisTraceTwo` the trace of Frobenius.

## What this file contains, and what it does not

⚠️ **The invariants themselves are no longer here.** They are
`EllipticCurves.TateModule.PrimaryDeterminant`, stated for an arbitrary prime `ℓ` in terms of one
input, `Nonempty (T_ℓE ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])`, which only the two non-degeneracy statements
consume. **This file supplies that input at `ℓ = 2` and contains no argument**: every proof below
is one line, and every definition below is *definitionally* its generic form at `ℓ = 2`. The input
is `nonempty_tateModuleEquivProd` (`EllipticCurves.TateModule.Free`).

⚠️ **Every public name and statement this file had before the extraction is unchanged.** Sixteen
declarations, same spellings, same types; consumers see no difference. This mirrors what
`EllipticCurves.TateModule.MatrixRep` did when the matrix transport moved to
`EllipticCurves.TateModule.PrimaryMatrixRep`, and what `EllipticCurves.TateModule.Free` did when
`padicPairEquiv` moved to `EllipticCurves.TateModule.PrimaryFree`.

## Non-degeneracy

Every statement here would be equally provable, and equally worthless, if `T₂E` were the zero
module: `LinearMap.det` is `1` and `LinearMap.trace` is `0` on modules that are not free and
finite, so `galoisDetTwo` and `galoisTraceTwo` are definable with no hypotheses whatsoever. The
statement that rules this out is `galoisTraceTwo_one`:

```
galoisTraceTwo (1 : G) = 2
```

which holds precisely because `Module.finrank ℤ_[2] T₂E = 2`
(`EllipticCurves.TateModule.Free`), and which is `0`, not `2`, for the zero module. It carries the
hypotheses `[IsAlgClosed F]`, `[(W'⁄F).IsElliptic]` and `(2 : F) ≠ 0` for exactly that reason.

⚠️ It is the **reason** the file needs any of them, but not the only statement that carries them:
`charpoly_galoisRepMatrixTwo_one` sits in the same `Nondegenerate` section and uses all three, in
the same way and for the same purpose — it passes `nonempty_tateModuleEquivProd h2` on. **Two**
declarations, one input. Everything above the `Non-degeneracy` section is a transport along an
equivalence and holds for a basis you were handed, whatever the basis is a basis of. That asymmetry
is what makes the extraction to `EllipticCurves.TateModule.PrimaryDeterminant` a one-hypothesis
affair.

## Using this file

The hypotheses live on the *base-changed* curve `W'⁄F`, and `WeierstrassCurve.baseChange` is a
plain `def`, so `[(W'⁄F).IsElliptic]` is **not** found by bare `inferInstance` even when
`[W'.IsElliptic]` is available. Use the idiom already standard in this development:

```
haveI : (W'⁄F).IsElliptic := inferInstanceAs (W'.map (algebraMap S F)).IsElliptic
```

## Scope

Only `ℓ = 2` *in this file*, and the `ℓ = 2` case went through the `2`-primary tower.

⚠️ **Three clauses this paragraph used to carry are now false and are replaced.** The first,
*"odd `ℓ` needs surjectivity of `[ℓ]` on `E(F̄)`, which is not available"*, is false at `ℓ = 3`:
`nsmul_three_surjective` (`EllipticCurves.Torsion.TriplingSurjective`) supplies it from
`(2 : F) ≠ 0` alone, and `EllipticCurves.Torsion.ThreePrimaryBasis` turns it into the coherent
system `T₃E` needs. The second, *"what is missing at `ℓ = 3` is the transport to `T₃E`"*, is false
as of `EllipticCurves.TateModule.FreeThree`, which performs that transport. The third, *"What is
missing at `ℓ = 3` is only that `galoisDetThree` is not stated below"*, is now false too:
`galoisDetThree` and `galoisTraceThree` **are** stated, in
`EllipticCurves.TateModule.DeterminantThree`, over the `ℓ`-generic invariants this file now shares
with them.

⚠️ Nothing is missing at `ℓ = 3` for the determinant and trace *themselves*. ⚠️ **The clause that
used to complete this sentence has been paid and is retired**: it read *"what remains `ℓ = 2` only
is the profinite packaging of the image (`EllipticCurves.TateModule.ImageProfinite`), and it is a
separate follow-up that nothing gates"*. That follow-up is
`EllipticCurves.TateModule.ImageProfiniteThree`, over the `ℓ`-generic
`EllipticCurves.TateModule.PrimaryImageProfinite`.
⚠️ This list used to include three more entries and no longer does. *"The basis-change conjugation
law (`EllipticCurves.TateModule.MatrixRepBasisChange`)"* is stated at every prime in
`EllipticCurves.TateModule.PrimaryMatrixRepBasisChange`; *"continuity
(`EllipticCurves.TateModule.MatrixContinuity`)"* is stated at every prime in
`EllipticCurves.TateModule.PrimaryMatrixContinuity`, with an `ℓ = 3` layer in
`EllipticCurves.TateModule.MatrixContinuityThree`; and *"`EllipticCurves.TateModule.Image`"* is
stated at every prime in `EllipticCurves.TateModule.PrimaryImage`, with an `ℓ = 3` layer in
`EllipticCurves.TateModule.ImageThree` — `isClosed_range_galoisDetThree` is there. ⚠️ **That last
one is not progress towards the cyclotomic-character identification**, which is what this file's
reader will hope: knowing the image of a character is closed says nothing about which character it
is. ⚠️ This paragraph used to continue *"at `ℓ ≥ 5` surjectivity is genuinely unavailable, because
it needs the general coordinate formula `x(ℓP) = Φ_ℓ/ΨSq_ℓ`"*, and that reason is false:
`[ℓ]`-surjectivity holds at every nonzero index with `(2 : F) ≠ 0`
(`nsmul_surjective_of_two_ne_zero`, `EllipticCurves.Torsion.TwoTorsionOrder`) and the formula is
proved at every index with `(2 : F) ≠ 0` (`hasXCoordFormula_of_two_ne_zero`,
`EllipticCurves.Torsion.NsmulOrder`).  ⚠️ **No replacement reason is asserted**: what a determinant
statement at `ℓ ≥ 5` costs was not re-measured here, and this file supplies nothing towards it
either way.

**Continuity is not asserted in this file**: `galoisRep` is built purely as a group homomorphism,
and passing to determinants changes nothing about that.

⚠️ **This paragraph used to say *"here or anywhere on this front"*, and that half is false.**
`EllipticCurves.TateModule.MatrixContinuity` proves `continuous_galoisDetTwo_of_basis` and
`continuous_galoisTraceTwo_of_basis` — continuity of `galoisDetTwo` and of `galoisTraceTwo`, the
two definitions of *this* file — with `continuous_galoisDetTwo` and `continuous_galoisTraceTwo`
removing the basis argument under `[IsAlgClosed F]`, `[(W'⁄F).IsElliptic]` and `(2 : F) ≠ 0`.
`EllipticCurves.TateModule.Continuity` proves `continuous_galoisRep`, which is about `galoisRep`
and so belongs to `EllipticCurves.TateModule.GaloisAction`, not to anything defined here. Every
one of the five carries `[Algebra.IsIntegral S F]`, which this file does not assume.

⚠️ **Neither module is nameable here, and the reason differs between them.**
`EllipticCurves.TateModule.MatrixContinuity` is **downstream**: it imports this file, and this
file does not import it. `EllipticCurves.TateModule.Continuity` is a **sibling**: neither imports
the other, and its whole `EllipticCurves` import closure is `EllipticCurves.TateModule.Basic`,
`EllipticCurves.TateModule.GaloisAction` and `EllipticCurves.Torsion.Defs`. So
`continuous_galoisDetTwo_of_basis`, `continuous_galoisTraceTwo_of_basis`, `continuous_galoisDetTwo`,
`continuous_galoisTraceTwo` and `continuous_galoisRep` are all forward references from this file,
and nothing below uses one. ⚠️ **That does not extend to the three closure modules just listed.**
They appear only as evidence for the sibling claim; all three are in *this* file's own import
closure, and this file uses two of them below — `galoisRep` is
`EllipticCurves.TateModule.GaloisAction`'s and `tateModule` is
`EllipticCurves.TateModule.Basic`'s. What remains true is the first half: continuity is not
asserted *here*.

**The identification of `galoisDetTwo` with the cyclotomic character is not proved here.** It is
the reason the determinant is interesting (Silverman, *AEC*, III.7 and III.8.1(a), (b), (d) —
⚠️ the identification is not itself a numbered result there; see the letter table in
`EllipticCurves.FunctionField.WeilPairing`). Nothing below
should be read as supplying it. Also out of scope: injectivity of `ρ_{E,2}`, and any description of
its image.

⚠️ This paragraph used to add "but it needs the Weil pairing and its Galois equivariance, none of
which is available yet", and that reason has expired: the pairing is Galois-equivariant in
cyclotomic form (`EllipticCurves.FunctionField.WeilPairingFunctionCyclotomic`), and
`EllipticCurves.FunctionField.WeilPairingDeterminant` proves the identification **mod `n`**, at
`n = 2` and `n = 3`, in coordinates. ⚠️ At `n = 3` it is no longer only in coordinates:
`EllipticCurves.FunctionField.WeilPairingDeterminantCharacter` (`#958`) proves
`galoisDetMod 3 = χ_3` as an identity of monoid homomorphisms `G →* (ZMod 3)ˣ`, with no basis and
no chosen pair in the statement. ⚠️ Be exact about which half that moves: it is the **mod-`3`**
half, and `galoisDetTwo = χ_2` over `ℤ_[2]` is untouched by it. What still blocks `galoisDetTwo`
itself is different and narrower: it is `LinearEquiv.det` on `T₂E`, so it needs the pairing at
**every** level `E[2 ^ k]` in order to take the inverse limit, and this development has the pairing
at `n = 2` and `n = 3` only. The gate is the general-`n` pairing, not the equivariance.

⚠️ **`galoisDetThree` existing does not move that gate either, and this file will now look as
though it does.** The `3`-adic identity `galoisDetThree = χ_3` over `ℤ_[3]` needs the pairing on
`E[3^k]` for **every** `k`, i.e. the pairing at composite `n`, exactly as at `ℓ = 2`. The mod-`3`
identity is a different statement about a different object (`galoisDetMod 3`, valued in
`(ZMod 3)ˣ`), and it landed separately.

## Main definitions

* `WeierstrassCurve.Affine.galoisDetTwo` : the determinant character `G →* ℤ_[2]ˣ`.
* `WeierstrassCurve.Affine.galoisTraceTwo` : the trace `G → ℤ_[2]`.

## Main statements

* `WeierstrassCurve.Affine.galoisRepMatrixTwo_eq_toMatrix` : the `GL₂`-valued representation is
  Mathlib's `LinearMap.toMatrix` of the Galois action.
* `WeierstrassCurve.Affine.coe_galoisDetTwo`,
  `WeierstrassCurve.Affine.trace_galoisRepMatrixTwo` : every basis computes the invariants.
* `WeierstrassCurve.Affine.det_galoisRepMatrixTwo_congr`,
  `WeierstrassCurve.Affine.trace_galoisRepMatrixTwo_congr`,
  `WeierstrassCurve.Affine.charpoly_galoisRepMatrixTwo_congr` : independence of the basis.
* `WeierstrassCurve.Affine.charpoly_galoisRepMatrixTwo` : `X² - (tr) X + (det)`.
* `WeierstrassCurve.Affine.galoisTraceTwo_one` : `tr ρ(1) = 2`, the rank-2 non-degeneracy witness.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7 and III.8.1.
-/

open Matrix Polynomial

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}

/-! ### The invariants -/

/-- **The determinant character of the `2`-adic representation**, `det ρ_{E,2} : G →* ℤ_[2]ˣ`.

This is `LinearEquiv.det` applied to the abstract representation `galoisRep 2`, so it involves no
choice of basis. `coe_galoisDetTwo` says that the determinant of the matrix `galoisRepMatrixTwo b σ`
computes it for every `b`; `det_galoisRepMatrixTwo_congr` is the resulting independence statement.
Definitionally `galoisDet` at `ℓ = 2`.

The identification of this character with the cyclotomic character needs the Weil pairing and is
**not** proved in this development. -/
noncomputable def galoisDetTwo : (F ≃ₐ[S] F) →* ℤ_[2]ˣ :=
  galoisDet (W' := W') (F := F) (ℓ := 2)

/-- **The trace of the `2`-adic representation**, `tr ρ_{E,2} : G → ℤ_[2]`.

Basis-free, like `galoisDetTwo`, since `LinearMap.trace` is. This is not a monoid homomorphism —
the trace is not multiplicative — which is why it is packaged as a bare function. Definitionally
`galoisTrace` at `ℓ = 2`. -/
noncomputable def galoisTraceTwo (σ : F ≃ₐ[S] F) : ℤ_[2] :=
  galoisTrace (W' := W') (F := F) (ℓ := 2) σ

theorem galoisDetTwo_apply (σ : F ≃ₐ[S] F) :
    galoisDetTwo (W' := W') (F := F) σ
      = LinearEquiv.det (M := (W'⁄F).tateModule 2) (galoisRep 2 σ) :=
  galoisDet_apply σ

/-- The determinant character is trivial at the identity — immediate, and recorded only for
symmetry with `galoisTraceTwo_one`. -/
@[simp]
theorem galoisDetTwo_one : galoisDetTwo (W' := W') (F := F) 1 = 1 := galoisDet_one

/-! ### Every basis computes the invariants -/

variable (b b' : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2))

/-- **The matrix representation is Mathlib's `LinearMap.toMatrix` of the Galois action.**

`galoisRepMatrixTwo` is built through `Matrix.GeneralLinearGroup.toLin'`, i.e. in the
matrix-to-linear-map direction; this identifies it with `LinearMap.toMatrix` in the other
direction, which is what all of Mathlib's determinant, trace and characteristic-polynomial API is
phrased in terms of. Everything else in this file follows from it. -/
theorem galoisRepMatrixTwo_eq_toMatrix (σ : F ≃ₐ[S] F) :
    (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2])
      = LinearMap.toMatrix b b ((galoisRep 2 σ : (W'⁄F).tateModule 2 ≃ₗ[ℤ_[2]] _) :
          (W'⁄F).tateModule 2 →ₗ[ℤ_[2]] (W'⁄F).tateModule 2) :=
  galoisRepMatrix_eq_toMatrix b σ

/-- **The determinant of the matrix computes the determinant character**, for every basis `b`. -/
theorem coe_galoisDetTwo (σ : F ≃ₐ[S] F) :
    ((galoisDetTwo (W' := W') (F := F) σ : ℤ_[2]ˣ) : ℤ_[2])
      = (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]).det :=
  coe_galoisDet b σ

/-- **The trace of the matrix computes the trace of the representation**, for every basis `b`. -/
theorem trace_galoisRepMatrixTwo (σ : F ≃ₐ[S] F) :
    (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]).trace
      = galoisTraceTwo (W' := W') (F := F) σ :=
  trace_galoisRepMatrix b σ

/-- **The characteristic polynomial of `ρ_{E,2}(σ)`**, in terms of the two canonical invariants.
Since the right-hand side does not mention `b`, neither does the characteristic polynomial. -/
theorem charpoly_galoisRepMatrixTwo (σ : F ≃ₐ[S] F) :
    (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]).charpoly
      = X ^ 2 - C (galoisTraceTwo (W' := W') (F := F) σ) * X
        + C ((galoisDetTwo (W' := W') (F := F) σ : ℤ_[2]ˣ) : ℤ_[2]) :=
  charpoly_galoisRepMatrix b σ

/-! ### Independence of the basis -/

/-- **`det ρ_{E,2}(σ)` does not depend on the basis.** -/
theorem det_galoisRepMatrixTwo_congr (σ : F ≃ₐ[S] F) :
    (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]).det
      = (galoisRepMatrixTwo b' σ : Matrix (Fin 2) (Fin 2) ℤ_[2]).det :=
  det_galoisRepMatrix_congr b b' σ

/-- **`tr ρ_{E,2}(σ)` does not depend on the basis.** -/
theorem trace_galoisRepMatrixTwo_congr (σ : F ≃ₐ[S] F) :
    (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]).trace
      = (galoisRepMatrixTwo b' σ : Matrix (Fin 2) (Fin 2) ℤ_[2]).trace :=
  trace_galoisRepMatrix_congr b b' σ

/-- **The characteristic polynomial of `ρ_{E,2}(σ)` does not depend on the basis.** -/
theorem charpoly_galoisRepMatrixTwo_congr (σ : F ≃ₐ[S] F) :
    (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]).charpoly
      = (galoisRepMatrixTwo b' σ : Matrix (Fin 2) (Fin 2) ℤ_[2]).charpoly :=
  charpoly_galoisRepMatrix_congr b b' σ

/-! ### Computation rules -/

/-- The determinant character in coordinates: the `2 × 2` determinant of the matrix whose columns
are the coordinate vectors of the Galois translates of the basis vectors. -/
theorem coe_galoisDetTwo_eq (σ : F ≃ₐ[S] F) :
    ((galoisDetTwo (W' := W') (F := F) σ : ℤ_[2]ˣ) : ℤ_[2])
      = b.repr (σ • b 0) 0 * b.repr (σ • b 1) 1 - b.repr (σ • b 1) 0 * b.repr (σ • b 0) 1 :=
  coe_galoisDet_eq b σ

/-- The trace in coordinates. -/
theorem galoisTraceTwo_eq (σ : F ≃ₐ[S] F) :
    galoisTraceTwo (W' := W') (F := F) σ = b.repr (σ • b 0) 0 + b.repr (σ • b 1) 1 :=
  galoisTrace_eq b σ

/-- The determinant of `galoisRepMatrixTwo b σ` is a unit — it is the value of a character with
values in `ℤ_[2]ˣ`. -/
theorem isUnit_det_galoisRepMatrixTwo (σ : F ≃ₐ[S] F) :
    IsUnit (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]).det :=
  isUnit_det_galoisRepMatrix b σ

/-! ### Non-degeneracy -/

section Nondegenerate

variable [IsAlgClosed F] [(W'⁄F).IsElliptic]

/-- **`tr ρ_{E,2}(1) = 2`.** This is the statement that pins down what the rest of the file is
about: it is `Module.finrank ℤ_[2] T₂E`, so it is `2` exactly because `T₂E` has rank two, and it
would be `0` if `T₂E` were the zero module — which is the degenerate case that `LinearMap.trace`
would otherwise silently allow.

⚠️ This is one of exactly **two** places in the file where `[IsAlgClosed F]`,
`[(W'⁄F).IsElliptic]` and `h2` are used at all — the other is
`charpoly_galoisRepMatrixTwo_one` below, which uses them identically. Both use them only to produce
`nonempty_tateModuleEquivProd h2`, which is the single hypothesis of
`galoisTrace_one_of_nonempty`. ⚠️ Measured, not assumed: putting `omit [IsAlgClosed F]` on
`charpoly_galoisRepMatrixTwo_one` gives `failed to synthesize instance of type class
IsAlgClosed F`. -/
theorem galoisTraceTwo_one (h2 : (2 : F) ≠ 0) :
    galoisTraceTwo (W' := W') (F := F) 1 = 2 :=
  galoisTrace_one_of_nonempty (tateModule.nonempty_tateModuleEquivProd h2)

/-- **The characteristic polynomial of the identity is `(X - 1)²`.** Written out as
`X² - 2X + 1`, this is `galoisTraceTwo_one` and `galoisDetTwo_one` combined, and is again a
statement that fails for the zero module. -/
theorem charpoly_galoisRepMatrixTwo_one (h2 : (2 : F) ≠ 0) :
    (galoisRepMatrixTwo b 1 : Matrix (Fin 2) (Fin 2) ℤ_[2]).charpoly
      = X ^ 2 - C 2 * X + C 1 :=
  charpoly_galoisRepMatrix_one_of_nonempty b (tateModule.nonempty_tateModuleEquivProd h2)

end Nondegenerate

end WeierstrassCurve.Affine
