/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.PrimaryMatrixRep
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The canonical invariants of `ρ_{E,ℓ}` at an arbitrary prime: determinant, trace, charpoly

`EllipticCurves.TateModule.PrimaryMatrixRep` produces the `ℓ`-adic Galois representation in matrix
form, `galoisRepMatrix b : G →* GL₂(ℤ_[ℓ])` for `G = F ≃ₐ[S] F`, but **only relative to a basis
`b`** of `T_ℓE`. There is no canonical basis: one comes from a coherent system of generating pairs
of the groups `E[ℓ^k]`, and two systems give representations differing by conjugation. So an
individual matrix entry of `galoisRepMatrix b σ` carries no information about `E` — it is an
artefact of the choice.

This file extracts what survives the choice, at **any** prime `ℓ`. The determinant and the trace of
a `ℤ_[ℓ]`-linear endomorphism are defined basis-free in Mathlib (`LinearEquiv.det`,
`LinearMap.trace`), so composing them with `galoisRep ℓ` gives honest invariants of the curve and
its Galois action:

```
galoisDet   : G →* ℤ_[ℓ]ˣ        the determinant character  det ρ_{E,ℓ}
galoisTrace : G → ℤ_[ℓ]          the trace                  tr  ρ_{E,ℓ}
```

and `coe_galoisDet` and `trace_galoisRepMatrix` say that for **every** basis `b` the corresponding
matrix quantity computes them.

## What this file is, and why it is `ℓ`-generic

This is the **extraction** of `EllipticCurves.TateModule.Determinant` to an arbitrary prime, and it
is the fourth link in a chain that has now worked four times: `EllipticCurves.Torsion.PrimaryBasis`
→ `EllipticCurves.TateModule.PrimaryFree` → `EllipticCurves.TateModule.PrimaryMatrixRep` → here.

⚠️ **Fourteen of the sixteen declarations of `Determinant.lean` mention `2` only in their types.**
The determinant, the trace, the identification with `LinearMap.toMatrix`, the characteristic
polynomial and all three basis-independence corollaries are transports along an equivalence and
have no arithmetic content whatsoever. Only the two non-degeneracy statements —
`galoisTrace_one_of_nonempty` and its charpoly corollary — consume anything prime-specific, and
what they consume is stated here as a **hypothesis**:

```
(h : Nonempty ((W'⁄F).tateModule ℓ ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ]))
```

That is the same hypothesis `exists_galoisRepMatrix_of_nonempty`
(`EllipticCurves.TateModule.PrimaryMatrixRep`) takes, and exactly what
`nonempty_tateModuleEquivProd_of_card` (`EllipticCurves.TateModule.PrimaryFree`) produces —
`nonempty_tateModuleEquivProd` at `ℓ = 2` and `nonempty_tateModuleEquivProd_three` at `ℓ = 3`.

⚠️ **This file supplies no `Nonempty (T_ℓE ≃ₗ ℤ_[ℓ]²)` at any prime**, so on its own it proves
nothing non-degenerate about any curve. The instances are
`EllipticCurves.TateModule.Determinant` (`ℓ = 2`) and
`EllipticCurves.TateModule.DeterminantThree` (`ℓ = 3`); at `ℓ ≥ 5` there is nothing to instantiate
with — see Scope.

## Non-degeneracy: why this file needs a hypothesis at all

⚠️ **This is the one place on this front where vacuity is not a formality.** Every statement above
the `Non-degeneracy` section would be equally provable, and equally worthless, if `T_ℓE` were the
zero module: `LinearMap.det` is `1` and `LinearMap.trace` is `0` on modules that are not free and
finite, so `galoisDet` and `galoisTrace` are definable **with no hypotheses whatsoever** and every
identity between them would hold. The statement that rules this out is

```
galoisTrace_one_of_nonempty : galoisTrace (1 : G) = 2
```

which holds precisely because `Module.finrank ℤ_[ℓ] T_ℓE = 2`, and which is `0`, not `2`, for the
zero module. ⚠️ It is the **only** reason this file takes a hypothesis, and it is why the
hypothesis is `Nonempty (T_ℓE ≃ₗ ℤ_[ℓ]²)` rather than `Module.Free` alone: freeness of the zero
module is not the obstruction, rank two is.

## Naming

⚠️ The rule is `EllipticCurves.TateModule.PrimaryMatrixRep`'s, and it is settled: **the generic
name is the `ℓ = 2` name with `Two` dropped, and takes `_of_nonempty` where it takes the new
hypothesis.** So `galoisDetTwo` becomes `galoisDet`, `trace_galoisRepMatrixTwo` becomes
`trace_galoisRepMatrix`, and `galoisTraceTwo_one` becomes `galoisTrace_one_of_nonempty`.

⚠️ `galoisDet` does not collide with `galoisDetMod` (`EllipticCurves.TateModule.DeterminantMod`),
which is the mod-`n` determinant of the action on `E[n]` and is a different object over a different
ring.

⚠️ **One consumer broke on this extraction even though no public statement moved, and it broke in a
way the previous extraction's recommended check does not see.** `galoisTraceTwo_eq_two_of_mem_ker`
(`EllipticCurves.TateModule.Kernel`) contained `unfold galoisTraceTwo`, which used to reach
`LinearMap.trace` in one step and now stops at `galoisTrace`. It is repaired to
`unfold galoisTraceTwo galoisTrace`. `EllipticCurves.TateModule.PrimaryMatrixRep`'s extraction
recorded `rw [<defName>]` and `simp only […, <defName>, …]` as the two forms to grep for before
moving a definition's body; ⚠️ **`unfold <defName>` is a third, and `delta` a fourth.** Grep all
four.

## Scope

* **No rank input.** See above: this file states the invariants and their computation rules, and
  takes rank two as a hypothesis exactly where it is needed.
* **Continuity is not asserted**, here or anywhere on this front: `galoisRep` is built purely as a
  group homomorphism and passing to determinants changes nothing about that. It is supplied
  downstream at `ℓ = 2` by `continuous_galoisDetTwo` in
  `EllipticCurves.TateModule.MatrixContinuity`; ⚠️ that file is still `ℓ = 2` only and this
  extraction does not make it generic.
* **The identification of `galoisDet` with the cyclotomic character is not proved here**, at any
  prime. See `EllipticCurves.TateModule.Determinant`'s Scope for what does and does not block it;
  ⚠️ the short version is that it needs the Weil pairing at **every** level `E[ℓ^k]`, and the
  mod-`n` identity is a different statement.
* Also out of scope: injectivity of `ρ_{E,ℓ}`, and any description of its image.
* ⚠️ **`ℓ ≥ 5` gains nothing from this file being generic.** Its hypothesis
  `Nonempty (T_ℓE ≃ₗ ℤ_[ℓ]²)` is gated at `ℓ ≥ 5` on `[ℓ]`-surjectivity and `#E[ℓ^k]`, both of
  which need the general coordinate formula `x(nP) = Φₙ/ΨSqₙ`, i.e. the `ωₙ` crux. What being
  generic buys is that when that gate is paid, the `ℓ = 5` file is a list of instantiations and no
  argument has to be written a third time.

## Using this file

The hypotheses of the instantiating files live on the *base-changed* curve `W'⁄F`, and
`WeierstrassCurve.baseChange` is a plain `def`, so `[(W'⁄F).IsElliptic]` is **not** found by bare
`inferInstance` even when `[W'.IsElliptic]` is available. Use the idiom already standard in this
development:

```
haveI : (W'⁄F).IsElliptic := inferInstanceAs (W'.map (algebraMap S F)).IsElliptic
```

⚠️ Note that **nothing in this file carries `[IsAlgClosed F]` or `[(W'⁄F).IsElliptic]`**, not even
`galoisTrace_one_of_nonempty`: those instances are how the *instantiating* files obtain the
`Nonempty` hypothesis, and this file is handed the conclusion. `Fact ℓ.Prime` is what `ℤ_[ℓ]` and
`galoisRep ℓ` require; Mathlib supplies it globally at `2` and at `3`.

## Main definitions

* `WeierstrassCurve.Affine.galoisDet` : the determinant character `G →* ℤ_[ℓ]ˣ`.
* `WeierstrassCurve.Affine.galoisTrace` : the trace `G → ℤ_[ℓ]`.

## Main statements

* `WeierstrassCurve.Affine.galoisRepMatrix_eq_toMatrix` : the `GL₂`-valued representation is
  Mathlib's `LinearMap.toMatrix` of the Galois action.
* `WeierstrassCurve.Affine.coe_galoisDet`, `WeierstrassCurve.Affine.trace_galoisRepMatrix` :
  every basis computes the invariants.
* `WeierstrassCurve.Affine.det_galoisRepMatrix_congr`,
  `WeierstrassCurve.Affine.trace_galoisRepMatrix_congr`,
  `WeierstrassCurve.Affine.charpoly_galoisRepMatrix_congr` : independence of the basis.
* `WeierstrassCurve.Affine.charpoly_galoisRepMatrix` : `X² - (tr) X + (det)`.
* `WeierstrassCurve.Affine.galoisTrace_one_of_nonempty` : `tr ρ(1) = 2`, the rank-two
  non-degeneracy witness and the only statement here that needs a hypothesis.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7 and III.8.1.
-/

open Matrix Polynomial

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
variable {ℓ : ℕ} [Fact ℓ.Prime]

/-! ### The invariants -/

/-- **The determinant character of the `ℓ`-adic representation**, `det ρ_{E,ℓ} : G →* ℤ_[ℓ]ˣ`.

This is `LinearEquiv.det` applied to the abstract representation `galoisRep ℓ`, so it involves no
choice of basis. `coe_galoisDet` says that the determinant of the matrix `galoisRepMatrix b σ`
computes it for every `b`; `det_galoisRepMatrix_congr` is the resulting independence statement.

The identification of this character with the cyclotomic character needs the Weil pairing and is
**not** proved in this development at any prime. -/
noncomputable def galoisDet : (F ≃ₐ[S] F) →* ℤ_[ℓ]ˣ :=
  (LinearEquiv.det : ((W'⁄F).tateModule ℓ ≃ₗ[ℤ_[ℓ]] (W'⁄F).tateModule ℓ) →* ℤ_[ℓ]ˣ).comp
    (galoisRep ℓ)

/-- **The trace of the `ℓ`-adic representation**, `tr ρ_{E,ℓ} : G → ℤ_[ℓ]`.

Basis-free, like `galoisDet`, since `LinearMap.trace` is. This is not a monoid homomorphism — the
trace is not multiplicative — which is why it is packaged as a bare function. -/
noncomputable def galoisTrace (σ : F ≃ₐ[S] F) : ℤ_[ℓ] :=
  LinearMap.trace ℤ_[ℓ] ((W'⁄F).tateModule ℓ)
    ((galoisRep ℓ σ : (W'⁄F).tateModule ℓ ≃ₗ[ℤ_[ℓ]] (W'⁄F).tateModule ℓ) :
      (W'⁄F).tateModule ℓ →ₗ[ℤ_[ℓ]] (W'⁄F).tateModule ℓ)

theorem galoisDet_apply (σ : F ≃ₐ[S] F) :
    galoisDet (W' := W') (F := F) (ℓ := ℓ) σ
      = LinearEquiv.det (M := (W'⁄F).tateModule ℓ) (galoisRep ℓ σ) := rfl

/-- The determinant character is trivial at the identity — immediate, and recorded only for
symmetry with `galoisTrace_one_of_nonempty`. ⚠️ Unlike that statement it needs no hypothesis, which
is precisely why it is *not* a non-degeneracy witness: it holds for the zero module too. -/
@[simp]
theorem galoisDet_one : galoisDet (W' := W') (F := F) (ℓ := ℓ) 1 = 1 := map_one _

/-! ### Every basis computes the invariants -/

variable (b b' : Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ))

/-- **The matrix representation is Mathlib's `LinearMap.toMatrix` of the Galois action.**

`galoisRepMatrix` is built through `Matrix.GeneralLinearGroup.toLin'`, i.e. in the
matrix-to-linear-map direction; this identifies it with `LinearMap.toMatrix` in the other
direction, which is what all of Mathlib's determinant, trace and characteristic-polynomial API is
phrased in terms of. Everything else in this file follows from it. -/
theorem galoisRepMatrix_eq_toMatrix (σ : F ≃ₐ[S] F) :
    (galoisRepMatrix b σ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ])
      = LinearMap.toMatrix b b ((galoisRep ℓ σ : (W'⁄F).tateModule ℓ ≃ₗ[ℤ_[ℓ]] _) :
          (W'⁄F).tateModule ℓ →ₗ[ℤ_[ℓ]] (W'⁄F).tateModule ℓ) := by
  ext i j
  rw [galoisRepMatrix_apply_coe, LinearMap.toMatrix_apply]
  rfl

/-- **The determinant of the matrix computes the determinant character**, for every basis `b`. -/
theorem coe_galoisDet (σ : F ≃ₐ[S] F) :
    ((galoisDet (W' := W') (F := F) (ℓ := ℓ) σ : ℤ_[ℓ]ˣ) : ℤ_[ℓ])
      = (galoisRepMatrix b σ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]).det := by
  rw [galoisRepMatrix_eq_toMatrix, LinearMap.det_toMatrix, galoisDet_apply, LinearEquiv.coe_det]

/-- **The trace of the matrix computes the trace of the representation**, for every basis `b`. -/
theorem trace_galoisRepMatrix (σ : F ≃ₐ[S] F) :
    (galoisRepMatrix b σ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]).trace
      = galoisTrace (W' := W') (F := F) (ℓ := ℓ) σ := by
  rw [galoisRepMatrix_eq_toMatrix, galoisTrace, LinearMap.trace_eq_matrix_trace ℤ_[ℓ] b]

/-- **The characteristic polynomial of `ρ_{E,ℓ}(σ)`**, in terms of the two canonical invariants.
Since the right-hand side does not mention `b`, neither does the characteristic polynomial. -/
theorem charpoly_galoisRepMatrix (σ : F ≃ₐ[S] F) :
    (galoisRepMatrix b σ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]).charpoly
      = X ^ 2 - C (galoisTrace (W' := W') (F := F) (ℓ := ℓ) σ) * X
        + C ((galoisDet (W' := W') (F := F) (ℓ := ℓ) σ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) := by
  rw [Matrix.charpoly_fin_two, trace_galoisRepMatrix, coe_galoisDet]

/-! ### Independence of the basis -/

/-- **`det ρ_{E,ℓ}(σ)` does not depend on the basis.** -/
theorem det_galoisRepMatrix_congr (σ : F ≃ₐ[S] F) :
    (galoisRepMatrix b σ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]).det
      = (galoisRepMatrix b' σ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]).det := by
  rw [← coe_galoisDet b, ← coe_galoisDet b']

/-- **`tr ρ_{E,ℓ}(σ)` does not depend on the basis.** -/
theorem trace_galoisRepMatrix_congr (σ : F ≃ₐ[S] F) :
    (galoisRepMatrix b σ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]).trace
      = (galoisRepMatrix b' σ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]).trace := by
  rw [trace_galoisRepMatrix b, trace_galoisRepMatrix b']

/-- **The characteristic polynomial of `ρ_{E,ℓ}(σ)` does not depend on the basis.** -/
theorem charpoly_galoisRepMatrix_congr (σ : F ≃ₐ[S] F) :
    (galoisRepMatrix b σ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]).charpoly
      = (galoisRepMatrix b' σ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]).charpoly := by
  rw [charpoly_galoisRepMatrix b, charpoly_galoisRepMatrix b']

/-! ### Computation rules -/

/-- The determinant character in coordinates: the `2 × 2` determinant of the matrix whose columns
are the coordinate vectors of the Galois translates of the basis vectors. -/
theorem coe_galoisDet_eq (σ : F ≃ₐ[S] F) :
    ((galoisDet (W' := W') (F := F) (ℓ := ℓ) σ : ℤ_[ℓ]ˣ) : ℤ_[ℓ])
      = b.repr (σ • b 0) 0 * b.repr (σ • b 1) 1 - b.repr (σ • b 1) 0 * b.repr (σ • b 0) 1 := by
  rw [coe_galoisDet b, Matrix.det_fin_two]
  simp only [galoisRepMatrix_apply_coe]

/-- The trace in coordinates. -/
theorem galoisTrace_eq (σ : F ≃ₐ[S] F) :
    galoisTrace (W' := W') (F := F) (ℓ := ℓ) σ = b.repr (σ • b 0) 0 + b.repr (σ • b 1) 1 := by
  rw [← trace_galoisRepMatrix b, Matrix.trace_fin_two]
  simp only [galoisRepMatrix_apply_coe]

/-- The determinant of `galoisRepMatrix b σ` is a unit — it is the value of a character with values
in `ℤ_[ℓ]ˣ`. -/
theorem isUnit_det_galoisRepMatrix (σ : F ≃ₐ[S] F) :
    IsUnit (galoisRepMatrix b σ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]).det := by
  rw [← coe_galoisDet b]
  exact (galoisDet (W' := W') (F := F) (ℓ := ℓ) σ).isUnit

/-! ### Non-degeneracy -/

/-- **`tr ρ_{E,ℓ}(1) = 2`.** This is the statement that pins down what the rest of the file is
about: it is `Module.finrank ℤ_[ℓ] T_ℓE`, so it is `2` exactly because `T_ℓE` has rank two, and it
would be `0` if `T_ℓE` were the zero module — which is the degenerate case that `LinearMap.trace`
would otherwise silently allow.

⚠️ It is the only statement in this file that takes a hypothesis, and the hypothesis is the whole
content: at `ℓ = 2` it is `nonempty_tateModuleEquivProd`, at `ℓ = 3` it is
`nonempty_tateModuleEquivProd_three`, and at `ℓ ≥ 5` nothing supplies it.

⚠️ **Deletion test**, measured on this file as committed. Deleting the hypothesis `h` from the
statement and replacing `obtain ⟨e⟩ := h` by
`obtain ⟨e⟩ : Nonempty ((W'⁄F).tateModule ℓ ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ]) := ?_` leaves, copy-paste:

```
error: don't know how to synthesize placeholder
context:
S : Type u_1
F : Type u_2
inst✝⁴ : Field S
inst✝³ : Field F
inst✝² : DecidableEq F
inst✝¹ : Algebra S F
W' : Affine S
ℓ : ℕ
inst✝ : Fact (Nat.Prime ℓ)
⊢ Nonempty (↥((W'⁄F).tateModule ℓ) ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])
```

⚠️ Two things accompany the deletion and neither adds information. First, `obtain ⟨e⟩ := h` becomes
`obtain ⟨e⟩ : Nonempty … := ?_`, so that a hole is legal where the hypothesis was; the type must be
written out rather than left as `_`, since nothing else in the goal determines it. Second, the
deletion *also* breaks `charpoly_galoisRepMatrix_one_of_nonempty` below, which passes `h` to
this theorem — a knock-on at a different declaration, **not** part of the measurement, and what a
consumer looks like when its input loses a hypothesis.

⚠️ The residual is a **goal** and not a type mismatch, and **nothing left in the context proves
it** — once `h` is gone the context has no curve-theoretic content at all, which is exactly the
point: without rank two the statement is *false* (the trace of the identity is `0` on the zero
module), not merely unproved. -/
theorem galoisTrace_one_of_nonempty
    (h : Nonempty ((W'⁄F).tateModule ℓ ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])) :
    galoisTrace (W' := W') (F := F) (ℓ := ℓ) 1 = 2 := by
  obtain ⟨e⟩ := h
  haveI : Module.Free ℤ_[ℓ] ((W'⁄F).tateModule ℓ) := Module.Free.of_equiv e.symm
  haveI : Module.Finite ℤ_[ℓ] ((W'⁄F).tateModule ℓ) := Module.Finite.equiv e.symm
  have hrank : Module.finrank ℤ_[ℓ] ((W'⁄F).tateModule ℓ) = 2 := by
    rw [e.finrank_eq, Module.finrank_prod, Module.finrank_self]
  have hid : ((galoisRep ℓ (1 : F ≃ₐ[S] F) : (W'⁄F).tateModule ℓ ≃ₗ[ℤ_[ℓ]] _) :
      (W'⁄F).tateModule ℓ →ₗ[ℤ_[ℓ]] (W'⁄F).tateModule ℓ) = LinearMap.id := by
    rw [map_one]; rfl
  rw [galoisTrace, hid, LinearMap.trace_id, hrank]
  norm_num

/-- **The characteristic polynomial of the identity is `(X - 1)²`.** Written out as `X² - 2X + 1`,
this is `galoisTrace_one_of_nonempty` and `galoisDet_one` combined, and is again a statement that
fails for the zero module. -/
theorem charpoly_galoisRepMatrix_one_of_nonempty
    (h : Nonempty ((W'⁄F).tateModule ℓ ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])) :
    (galoisRepMatrix b 1 : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]).charpoly = X ^ 2 - C 2 * X + C 1 := by
  rw [charpoly_galoisRepMatrix b, galoisTrace_one_of_nonempty h, galoisDet_one, Units.val_one]

end WeierstrassCurve.Affine
