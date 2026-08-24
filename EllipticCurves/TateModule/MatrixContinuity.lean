/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.Continuity
import EllipticCurves.TateModule.Determinant
import EllipticCurves.TateModule.MatrixRep
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# `ρ_{E,2} : G → GL₂(ℤ_[2])` is continuous for the `2`-adic topology

`EllipticCurves.TateModule.MatrixRep` builds the matrix form `galoisRepMatrixTwo b` of the `2`-adic
Galois representation out of a basis `b` of `T₂E`, as a homomorphism of abstract groups;
`EllipticCurves.TateModule.Continuity` proves that the *abstract* representation
`galoisRep 2 : G →* Aut(T₂E)` is continuous for the profinite topology on `T₂E`. Neither says
anything about `GL₂(ℤ_[2])` with its `2`-adic topology, which is what "the `2`-adic representation"
classically means. This file closes that gap.

## The obstruction that was not there

Three previous files each excluded this as a stretch goal with the same stated reason: that the
compact-bijection-is-a-homeomorphism argument is circular, because it needs the continuity of
`b.repr` that one is trying to prove, and that one would therefore first have to construct a basis
compatible with the level filtration.

The argument is not circular; it simply runs in the other direction. The map
`b.equivFun.symm : ℤ_[2]² → T₂E` is continuous **for free** — it is `x ↦ ∑ i, x i • b i`, and
`T_ℓE` is already known to be a topological `ℤ_[ℓ]`-module
(`tateModule.instContinuousSMulPadicInt`). Its *source* `Fin 2 → ℤ_[2]` is compact
(`PadicInt.compactSpace`), and its *target* `T₂E` is Hausdorff (`tateModule.t2Space`). A continuous
bijection from a compact space to a Hausdorff space is a homeomorphism, so `b.equivFun` is
continuous by inversion. The compactness consumed is that of `ℤ_[2]²`, not that of `T₂E`, and no
level-compatible basis is needed: **any** basis works.

## What is proved

* `tateModule.coordHomeomorph` — `T₂E ≃ₜ (Fin 2 → ℤ_[2])`, and
  `tateModule.coordContinuousLinearEquiv` — the same map as a `ℤ_[2]`-linear homeomorphism. This is
  the substance: *the profinite topology on `T₂E` is the `2`-adic topology of a free `ℤ_[2]`-module
  of rank `2`*. Everything else is a corollary.
* `continuous_galoisRepMatrixTwo` — `ρ_{E,2} : G →* GL₂(ℤ_[2])` is continuous, for the Krull
  topology on `G` and the topology `GL₂(ℤ_[2])` inherits from `ℤ_[2]` through
  `Units.instTopologicalSpaceUnits`.
* `continuous_galoisDetTwo`, `continuous_galoisTraceTwo` — the invariants of
  `EllipticCurves.TateModule.Determinant` are continuous.
* `exists_continuous_galoisRepMatrixTwo` — the choice-free capstone, the continuous refinement of
  `exists_galoisRepMatrixTwo`.

This supersedes the remark "Continuity is not asserted" in `galoisRepMatrixTwo`'s docstring. That
file is not edited here.

## Non-degeneracy

`Continuous ρ` is true whenever `G = F ≃ₐ[S] F` is trivial, and no theorem about `G` alone can
exclude that: it is a fact about the extension `F / S`, not about the curve. The capstone therefore
keeps the compatibility clause `⇑(b.repr (σ • f)) = ↑(ρ σ) *ᵥ ⇑(b.repr f)` — without it,
`∃ ρ, Continuous ρ` is witnessed by the trivial homomorphism and mentions neither the curve nor its
Tate module.

The reading that *this file* must exclude is a different one: that continuity into `GL₂(ℤ_[2])` is
automatic. It would be, if the codomain were discrete — and that is exactly the situation of
`continuous_galoisRepMod`, where `E[n]` carries the discrete topology and continuity is only
levelwise local constancy. It is not the situation here, and
`Matrix.GeneralLinearGroup.not_discreteTopology_padicInt` says so: `GL₂(ℤ_[p])` is not discrete,
because the unipotent line `x ↦ !![1, x; 0, 1]` embeds the non-discrete `ℤ_[p]` into it. So the
statement proved here is a genuine constraint on `ρ_{E,2}`, not a formality.

On the source side the same discrimination is already available: `T₂E` is not discrete
(`tateModule.not_discreteTopology_tateModule_two`, from `EllipticCurves.TateModule.Profinite`), so
`coordHomeomorph` is not a homeomorphism between discrete spaces either.

## Scope

`ℓ = 2` only, because the statements below are. ⚠️ **Two clauses this paragraph used to carry are
false and are replaced.** The first, *"Odd `ℓ` needs `T_ℓE ≅ ℤ_ℓ²`, which is gated on the
finiteness of `E[ℓ^k]`"*, is false at `ℓ = 3` on both counts: `E[3^k]` is finite
(`finite_torsion_three_pow`, `EllipticCurves.Torsion.ThreePrimary`) and `T₃E ≅ ℤ₃²` is proved
(`EllipticCurves.TateModule.FreeThree`). The second, *"What is missing at `ℓ = 3` is the matrix
representation `galoisRepMatrixThree`, which nothing in this development states yet"*, is false
too: it is stated, in `EllipticCurves.TateModule.MatrixRepThree`, over the `ℓ`-generic transport
`EllipticCurves.TateModule.PrimaryMatrixRep`.

⚠️ **What is missing at `ℓ = 3` is therefore continuity itself, i.e. this file.** Its inputs
`tateModule.instContinuousSMulPadicInt` and `tateModule.continuous_galois_smul` are already
`ℓ`-generic, and `galoisRepMatrixThree`, `galoisDetThree` and `galoisTraceThree` now all exist, so
nothing here is blocked.

⚠️ **A third clause, added when the second was repaired, was also false and is replaced.** It read
*"plus the profinite side of `T₃E`, which is a different dependency — see
`EllipticCurves.TateModule.Profinite`, still `ℓ = 2` only"*. Two things wrong with it: this file
does not reach `EllipticCurves.TateModule.Profinite` at all — not directly and not transitively,
measured by walking the `import` graph — so no proof below can consume anything from it and the
single mention above is a prose cross-reference; and that file is **not** `ℓ = 2`
only — its `variable` block is `(W : Affine F) (ℓ : ℕ)` and `compactSpace`, `isCompact_coe`,
`levelFamily` and `isClosedEmbedding_levelFamily` are all stated at an arbitrary prime. Only four
*instantiations* there are `ℓ = 2` — `compactSpace_two`, `not_discreteTopology_tateModule_two`,
`profiniteAddGrpTwo` and `coe_profiniteAddGrpTwo`.

⚠️ **The conclusion it was offered for is nonetheless right**: the `ℓ = 3` twin of this file is a
genuine follow-up rather than a one-line instantiation, because this file proves
`continuous_galoisDetTwo` and `continuous_galoisTraceTwo` as well as
`continuous_galoisRepMatrixTwo`, and each of the eighteen declarations below has to be restated.
It is work, not a gate. At `ℓ ≥ 5` the gate is real and it is the general coordinate formula
`x(ℓP) = Φ_ℓ/ΨSq_ℓ`, not finiteness alone.

Everything is stated for a base change `W'⁄F` of a curve `W' : Affine S` rather than for a bare
`W : Affine F`, matching the representation section of `EllipticCurves.TateModule.MatrixRep`. This
is forced: `tateModule.instContinuousSMulPadicInt` and `tateModule.continuous_galois_smul` are
themselves stated about `(W'⁄F).tateModule ℓ`, and instance search will not unify a bare `W` with
`?W'.baseChange F`.

Not proved here: that `det ρ_{E,2}` is the cyclotomic character (Weil-pairing gated); that the image
of `ρ_ℓ` is open or closed (`G` is not known compact); that `ρ_{E,2}` is locally constant (it is
not — see `EllipticCurves.TateModule.OpenKernel`).

## Main statements

* `WeierstrassCurve.Affine.tateModule.coordHomeomorph`
* `WeierstrassCurve.Affine.tateModule.coordContinuousLinearEquiv`
* `WeierstrassCurve.Affine.continuous_galoisRepMatrixTwo`
* `WeierstrassCurve.Affine.exists_continuous_galoisRepMatrixTwo`

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open Matrix

open scoped WeierstrassCurve.Affine.ProfiniteTopology

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}

namespace tateModule

variable (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2))

/-! ### The coordinate homeomorphism `T₂E ≃ₜ ℤ_[2]²` -/

/-- **Reading a coordinate vector back into `T₂E` is continuous.** This is the free half of the
coordinate homeomorphism: `b.equivFun.symm x = ∑ i, x i • b i`, and `T₂E` is a topological
`ℤ_[2]`-module. -/
theorem continuous_equivFun_symm :
    Continuous (b.equivFun.symm : (Fin 2 → ℤ_[2]) → (W'⁄F).tateModule 2) := by
  have h : (b.equivFun.symm : (Fin 2 → ℤ_[2]) → (W'⁄F).tateModule 2)
      = fun x => ∑ i, x i • b i := funext fun x => b.equivFun_symm_apply x
  rw [h]
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const

/-- **The profinite topology on `T₂E` is the `2`-adic topology of `ℤ_[2]²`.**

`continuous_equivFun_symm` is a continuous bijection out of the compact space `Fin 2 → ℤ_[2]`
(`PadicInt.compactSpace` and `Pi.compactSpace`) into the Hausdorff space `T₂E`
(`tateModule.t2Space`), hence a homeomorphism.

This is where the supposed circularity of the compact-to-Hausdorff argument dissolves: the
compactness used is that of the *coordinate space*, which Mathlib supplies, so no basis compatible
with the level filtration has to be constructed first. -/
noncomputable def coordHomeomorph : (W'⁄F).tateModule 2 ≃ₜ (Fin 2 → ℤ_[2]) :=
  (Continuous.homeoOfEquivCompactToT2 (f := b.equivFun.symm.toEquiv)
    (continuous_equivFun_symm b)).symm

@[simp]
theorem coe_coordHomeomorph :
    (coordHomeomorph b : (W'⁄F).tateModule 2 → (Fin 2 → ℤ_[2])) = b.equivFun := rfl

@[simp]
theorem coe_coordHomeomorph_symm :
    ((coordHomeomorph b).symm : (Fin 2 → ℤ_[2]) → (W'⁄F).tateModule 2) = b.equivFun.symm := rfl

/-- **Taking coordinates is continuous.** The half that needed the compactness argument. -/
theorem continuous_equivFun :
    Continuous (b.equivFun : (W'⁄F).tateModule 2 → (Fin 2 → ℤ_[2])) :=
  (coordHomeomorph b).continuous

/-- Each coordinate function `f ↦ b.repr f i` is continuous. This is the form the matrix entries
are read through. -/
theorem continuous_repr_apply (i : Fin 2) :
    Continuous fun f : (W'⁄F).tateModule 2 => b.repr f i :=
  (continuous_apply i).comp (continuous_equivFun b)

/-- **`T₂E` is topologically a free `ℤ_[2]`-module of rank `2`**: the coordinate isomorphism
attached to a basis is a homeomorphism, so it is an isomorphism of topological `ℤ_[2]`-modules.

This is the packaged form of `coordHomeomorph`, and the form a consumer wants: it carries the
`ℤ_[2]`-linearity that `Homeomorph` alone does not. -/
noncomputable def coordContinuousLinearEquiv :
    (W'⁄F).tateModule 2 ≃L[ℤ_[2]] (Fin 2 → ℤ_[2]) where
  toLinearEquiv := b.equivFun
  continuous_toFun := continuous_equivFun b
  continuous_invFun := continuous_equivFun_symm b

@[simp]
theorem coe_coordContinuousLinearEquiv :
    (coordContinuousLinearEquiv b : (W'⁄F).tateModule 2 → (Fin 2 → ℤ_[2])) = b.equivFun := rfl

@[simp]
theorem coordContinuousLinearEquiv_toLinearEquiv :
    (coordContinuousLinearEquiv b).toLinearEquiv = b.equivFun := rfl

end tateModule

/-! ### Continuity of the matrix representation -/

variable [Algebra.IsIntegral S F]
variable (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2))

/-- **The matrix of `ρ_{E,2}(σ)` depends continuously on `σ`.**

Entrywise: `(ρ σ) i j = b.repr (σ • b j) i` is the composite of the continuous orbit map
`σ ↦ σ • b j` with the continuous coordinate function. -/
theorem continuous_galoisRepMatrixTwo_coe :
    Continuous fun σ : F ≃ₐ[S] F =>
      (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]) := by
  refine continuous_matrix fun i j => ?_
  simp only [galoisRepMatrixTwo_apply_coe]
  exact (tateModule.continuous_repr_apply b i).comp (tateModule.continuous_galois_smul 2 (b j))

/-- **`ρ_{E,2} : G →* GL₂(ℤ_[2])` is continuous**, for the Krull topology on `G` and the `2`-adic
topology on `GL₂(ℤ_[2])`.

This is the classical statement that `galoisRepMatrixTwo` was one step short of. `GL` carries the
topology induced from `Matrix × Matrix` by `u ↦ (u, u⁻¹)`, so both the matrix and its inverse must
vary continuously; the inverse costs nothing, since `↑(ρ σ)⁻¹ = ↑(ρ σ⁻¹)` and inversion is
continuous in the topological group `G`. -/
theorem continuous_galoisRepMatrixTwo : Continuous (galoisRepMatrixTwo b) := by
  rw [Units.continuous_iff]
  refine ⟨continuous_galoisRepMatrixTwo_coe b, ?_⟩
  simp_rw [← map_inv]
  exact (continuous_galoisRepMatrixTwo_coe b).comp continuous_inv

/-! ### The invariants are continuous -/

/-- **The determinant character `det ρ_{E,2} : G →* ℤ_[2]ˣ` is continuous.**

`galoisDetTwo` is basis-free, but its continuity is proved through a basis, which is why one is
taken as an argument; `continuous_galoisDetTwo` removes it at `ℓ = 2`. -/
theorem continuous_galoisDetTwo_of_basis
    (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2)) :
    Continuous (galoisDetTwo (W' := W') (F := F)) := by
  rw [Units.continuous_iff]
  constructor
  · simp only [Function.comp_def, coe_galoisDetTwo b]
    exact (continuous_galoisRepMatrixTwo_coe b).matrix_det
  · simp_rw [← map_inv, coe_galoisDetTwo b]
    exact ((continuous_galoisRepMatrixTwo_coe b).comp continuous_inv).matrix_det

/-- **The trace `tr ρ_{E,2} : G → ℤ_[2]` is continuous.** Unlike the determinant this is not a
homomorphism, so there is no unit-topology bookkeeping: it is the matrix trace of a continuously
varying matrix. -/
theorem continuous_galoisTraceTwo_of_basis
    (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2)) :
    Continuous (galoisTraceTwo (W' := W') (F := F)) := by
  have h : (galoisTraceTwo (W' := W') (F := F))
      = fun σ => (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]).trace :=
    funext fun σ => (trace_galoisRepMatrixTwo b σ).symm
  rw [h]
  exact (continuous_galoisRepMatrixTwo_coe b).matrix_trace

/-! ### The unconditional `ℓ = 2` layer and the capstone -/

section Two

variable [IsAlgClosed F] [(W'⁄F).IsElliptic]

/-- `det ρ_{E,2}` is continuous, with no basis supplied: over an algebraically closed field of
characteristic `≠ 2` a basis exists (`nonempty_basis_tateModule_two`), and continuity is a `Prop`,
so the choice can be discharged. -/
theorem continuous_galoisDetTwo (h2 : (2 : F) ≠ 0) :
    Continuous (galoisDetTwo (W' := W') (F := F)) := by
  obtain ⟨b⟩ := tateModule.nonempty_basis_tateModule_two (W := W'⁄F) h2
  exact continuous_galoisDetTwo_of_basis b

/-- `tr ρ_{E,2}` is continuous, with no basis supplied. -/
theorem continuous_galoisTraceTwo (h2 : (2 : F) ≠ 0) :
    Continuous (galoisTraceTwo (W' := W') (F := F)) := by
  obtain ⟨b⟩ := tateModule.nonempty_basis_tateModule_two (W := W'⁄F) h2
  exact continuous_galoisTraceTwo_of_basis b

/-- **`ρ_{E,2}` is a continuous `2`-adic matrix representation.**

The continuous refinement of `exists_galoisRepMatrixTwo`: there are a basis of `T₂E` and a
**continuous** homomorphism `ρ : G →* GL₂(ℤ_[2])` whose matrices compute the Galois action on
coordinate vectors.

The compatibility clause is load-bearing. `∃ ρ, Continuous ρ` alone is witnessed by the trivial
homomorphism and would mention neither the curve nor its Tate module; it is the clause that ties
`ρ` to `σ • ·` on `T₂E`. -/
theorem exists_continuous_galoisRepMatrixTwo (h2 : (2 : F) ≠ 0) :
    ∃ (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2))
      (ρ : (F ≃ₐ[S] F) →* GL (Fin 2) ℤ_[2]), Continuous ρ ∧
        ∀ (σ : F ≃ₐ[S] F) (f : (W'⁄F).tateModule 2),
          ⇑(b.repr (σ • f)) = (ρ σ : Matrix (Fin 2) (Fin 2) ℤ_[2]) *ᵥ ⇑(b.repr f) := by
  obtain ⟨b⟩ := tateModule.nonempty_basis_tateModule_two (W := W'⁄F) h2
  exact ⟨b, galoisRepMatrixTwo b, continuous_galoisRepMatrixTwo b, galoisRepMatrixTwo_mulVec b⟩

end Two

end WeierstrassCurve.Affine

/-! ### The codomain is not discrete

Continuity into a discrete space is no constraint at all, and that is precisely the situation of
`continuous_galoisRepMod`, whose codomain `E[n]` is discrete. The results above are not of that
kind, and this section is the certificate. -/

/-- `ℤ_[p]` is not discrete: it is compact and infinite. -/
theorem PadicInt.not_discreteTopology (p : ℕ) [Fact p.Prime] :
    ¬ DiscreteTopology ℤ_[p] := fun h =>
  @not_finite ℤ_[p] _ (@finite_of_compact_of_discrete _ _ _ h)

/-- **`GL₂(ℤ_[p])` is not discrete.** The unipotent line `x ↦ !![1, x; 0, 1]` is a continuous
injection of `ℤ_[p]` into it, so a discrete `GL₂` would force `{0}` open in `ℤ_[p]` and hence — the
latter being a topological additive group — `ℤ_[p]` itself discrete.

This is what makes `continuous_galoisRepMatrixTwo` a statement rather than a formality. -/
theorem Matrix.GeneralLinearGroup.not_discreteTopology_padicInt (p : ℕ) [Fact p.Prime] :
    ¬ DiscreteTopology (GL (Fin 2) ℤ_[p]) := by
  intro h
  refine PadicInt.not_discreteTopology p ?_
  refine discreteTopology_of_isOpen_singleton_zero ?_
  have hpre : (upperRightHom (R := ℤ_[p])) ⁻¹' {upperRightHom (0 : ℤ_[p])} = {0} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, injective_upperRightHom.eq_iff]
  rw [← hpre]
  exact continuous_upperRightHom.isOpen_preimage _ (isOpen_discrete _)
