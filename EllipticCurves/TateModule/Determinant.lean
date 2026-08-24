/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.MatrixRep
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

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

## Using this file

The hypotheses live on the *base-changed* curve `W'⁄F`, and `WeierstrassCurve.baseChange` is a
plain `def`, so `[(W'⁄F).IsElliptic]` is **not** found by bare `inferInstance` even when
`[W'.IsElliptic]` is available. Use the idiom already standard in this development:

```
haveI : (W'⁄F).IsElliptic := inferInstanceAs (W'.map (algebraMap S F)).IsElliptic
```

## Scope

Only `ℓ = 2`; odd `ℓ` needs surjectivity of `[ℓ]` on `E(F̄)`, which is not available.

**Continuity is not asserted**, here or anywhere on this front: `galoisRep` is built purely as a
group homomorphism, and passing to determinants changes nothing about that.

**The identification of `galoisDetTwo` with the cyclotomic character is not proved here.** It is
the reason the determinant is interesting (Silverman, *AEC*, III.7 and III.8.1). Nothing below
should be read as supplying it. Also out of scope: injectivity of `ρ_{E,2}`, and any description of
its image.

⚠️ This paragraph used to add "but it needs the Weil pairing and its Galois equivariance, none of
which is available yet", and that reason has expired: the pairing is Galois-equivariant in
cyclotomic form (`EllipticCurves.FunctionField.WeilPairingFunctionCyclotomic`), and
`EllipticCurves.FunctionField.WeilPairingDeterminant` proves the identification **mod `n`**, at
`n = 2` and `n = 3`, in coordinates. What still blocks `galoisDetTwo` itself is different and
narrower: it is `LinearEquiv.det` on `T₂E`, so it needs the pairing at **every** level `E[2 ^ k]`
in order to take the inverse limit, and this development has the pairing at `n = 2` and `n = 3`
only. The gate is the general-`n` pairing, not the equivariance.

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

The identification of this character with the cyclotomic character needs the Weil pairing and is
**not** proved in this development. -/
noncomputable def galoisDetTwo : (F ≃ₐ[S] F) →* ℤ_[2]ˣ :=
  (LinearEquiv.det : ((W'⁄F).tateModule 2 ≃ₗ[ℤ_[2]] (W'⁄F).tateModule 2) →* ℤ_[2]ˣ).comp
    (galoisRep 2)

/-- **The trace of the `2`-adic representation**, `tr ρ_{E,2} : G → ℤ_[2]`.

Basis-free, like `galoisDetTwo`, since `LinearMap.trace` is. This is not a monoid homomorphism —
the trace is not multiplicative — which is why it is packaged as a bare function. -/
noncomputable def galoisTraceTwo (σ : F ≃ₐ[S] F) : ℤ_[2] :=
  LinearMap.trace ℤ_[2] ((W'⁄F).tateModule 2)
    ((galoisRep 2 σ : (W'⁄F).tateModule 2 ≃ₗ[ℤ_[2]] (W'⁄F).tateModule 2) :
      (W'⁄F).tateModule 2 →ₗ[ℤ_[2]] (W'⁄F).tateModule 2)

theorem galoisDetTwo_apply (σ : F ≃ₐ[S] F) :
    galoisDetTwo (W' := W') (F := F) σ
      = LinearEquiv.det (M := (W'⁄F).tateModule 2) (galoisRep 2 σ) := rfl

/-- The determinant character is trivial at the identity — immediate, and recorded only for
symmetry with `galoisTraceTwo_one`. -/
@[simp]
theorem galoisDetTwo_one : galoisDetTwo (W' := W') (F := F) 1 = 1 := map_one _

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
          (W'⁄F).tateModule 2 →ₗ[ℤ_[2]] (W'⁄F).tateModule 2) := by
  ext i j
  rw [galoisRepMatrixTwo_apply_coe, LinearMap.toMatrix_apply]
  rfl

/-- **The determinant of the matrix computes the determinant character**, for every basis `b`. -/
theorem coe_galoisDetTwo (σ : F ≃ₐ[S] F) :
    ((galoisDetTwo (W' := W') (F := F) σ : ℤ_[2]ˣ) : ℤ_[2])
      = (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]).det := by
  rw [galoisRepMatrixTwo_eq_toMatrix, LinearMap.det_toMatrix, galoisDetTwo_apply,
    LinearEquiv.coe_det]

/-- **The trace of the matrix computes the trace of the representation**, for every basis `b`. -/
theorem trace_galoisRepMatrixTwo (σ : F ≃ₐ[S] F) :
    (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]).trace
      = galoisTraceTwo (W' := W') (F := F) σ := by
  rw [galoisRepMatrixTwo_eq_toMatrix, galoisTraceTwo, LinearMap.trace_eq_matrix_trace ℤ_[2] b]

/-- **The characteristic polynomial of `ρ_{E,2}(σ)`**, in terms of the two canonical invariants.
Since the right-hand side does not mention `b`, neither does the characteristic polynomial. -/
theorem charpoly_galoisRepMatrixTwo (σ : F ≃ₐ[S] F) :
    (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]).charpoly
      = X ^ 2 - C (galoisTraceTwo (W' := W') (F := F) σ) * X
        + C ((galoisDetTwo (W' := W') (F := F) σ : ℤ_[2]ˣ) : ℤ_[2]) := by
  rw [Matrix.charpoly_fin_two, trace_galoisRepMatrixTwo, coe_galoisDetTwo]

/-! ### Independence of the basis -/

/-- **`det ρ_{E,2}(σ)` does not depend on the basis.** -/
theorem det_galoisRepMatrixTwo_congr (σ : F ≃ₐ[S] F) :
    (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]).det
      = (galoisRepMatrixTwo b' σ : Matrix (Fin 2) (Fin 2) ℤ_[2]).det := by
  rw [← coe_galoisDetTwo b, ← coe_galoisDetTwo b']

/-- **`tr ρ_{E,2}(σ)` does not depend on the basis.** -/
theorem trace_galoisRepMatrixTwo_congr (σ : F ≃ₐ[S] F) :
    (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]).trace
      = (galoisRepMatrixTwo b' σ : Matrix (Fin 2) (Fin 2) ℤ_[2]).trace := by
  rw [trace_galoisRepMatrixTwo b, trace_galoisRepMatrixTwo b']

/-- **The characteristic polynomial of `ρ_{E,2}(σ)` does not depend on the basis.** -/
theorem charpoly_galoisRepMatrixTwo_congr (σ : F ≃ₐ[S] F) :
    (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]).charpoly
      = (galoisRepMatrixTwo b' σ : Matrix (Fin 2) (Fin 2) ℤ_[2]).charpoly := by
  rw [charpoly_galoisRepMatrixTwo b, charpoly_galoisRepMatrixTwo b']

/-! ### Computation rules -/

/-- The determinant character in coordinates: the `2 × 2` determinant of the matrix whose columns
are the coordinate vectors of the Galois translates of the basis vectors. -/
theorem coe_galoisDetTwo_eq (σ : F ≃ₐ[S] F) :
    ((galoisDetTwo (W' := W') (F := F) σ : ℤ_[2]ˣ) : ℤ_[2])
      = b.repr (σ • b 0) 0 * b.repr (σ • b 1) 1 - b.repr (σ • b 1) 0 * b.repr (σ • b 0) 1 := by
  rw [coe_galoisDetTwo b, Matrix.det_fin_two]
  simp only [galoisRepMatrixTwo_apply_coe]

/-- The trace in coordinates. -/
theorem galoisTraceTwo_eq (σ : F ≃ₐ[S] F) :
    galoisTraceTwo (W' := W') (F := F) σ = b.repr (σ • b 0) 0 + b.repr (σ • b 1) 1 := by
  rw [← trace_galoisRepMatrixTwo b, Matrix.trace_fin_two]
  simp only [galoisRepMatrixTwo_apply_coe]

/-- The determinant of `galoisRepMatrixTwo b σ` is a unit — it is the value of a character with
values in `ℤ_[2]ˣ`. -/
theorem isUnit_det_galoisRepMatrixTwo (σ : F ≃ₐ[S] F) :
    IsUnit (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]).det := by
  rw [← coe_galoisDetTwo b]
  exact (galoisDetTwo (W' := W') (F := F) σ).isUnit

/-! ### Non-degeneracy -/

section Nondegenerate

variable [IsAlgClosed F] [(W'⁄F).IsElliptic]

/-- **`tr ρ_{E,2}(1) = 2`.** This is the statement that pins down what the rest of the file is
about: it is `Module.finrank ℤ_[2] T₂E`, so it is `2` exactly because `T₂E` has rank two, and it
would be `0` if `T₂E` were the zero module — which is the degenerate case that `LinearMap.trace`
would otherwise silently allow. -/
theorem galoisTraceTwo_one (h2 : (2 : F) ≠ 0) :
    galoisTraceTwo (W' := W') (F := F) 1 = 2 := by
  haveI := tateModule.free_tateModule_two (W := W'⁄F) h2
  haveI := tateModule.finite_tateModule_two (W := W'⁄F) h2
  have h : ((galoisRep 2 (1 : F ≃ₐ[S] F) : (W'⁄F).tateModule 2 ≃ₗ[ℤ_[2]] _) :
      (W'⁄F).tateModule 2 →ₗ[ℤ_[2]] (W'⁄F).tateModule 2) = LinearMap.id := by
    rw [map_one]; rfl
  rw [galoisTraceTwo, h, LinearMap.trace_id, tateModule.finrank_tateModule_two h2]
  norm_num

/-- **The characteristic polynomial of the identity is `(X - 1)²`.** Written out as
`X² - 2X + 1`, this is `galoisTraceTwo_one` and `galoisDetTwo_one` combined, and is again a
statement that fails for the zero module. -/
theorem charpoly_galoisRepMatrixTwo_one (h2 : (2 : F) ≠ 0) :
    (galoisRepMatrixTwo b 1 : Matrix (Fin 2) (Fin 2) ℤ_[2]).charpoly
      = X ^ 2 - C 2 * X + C 1 := by
  rw [charpoly_galoisRepMatrixTwo b, galoisTraceTwo_one h2, galoisDetTwo_one, Units.val_one]

end Nondegenerate

end WeierstrassCurve.Affine
