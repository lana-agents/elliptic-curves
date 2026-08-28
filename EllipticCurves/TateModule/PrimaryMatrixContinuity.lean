/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.Continuity
import EllipticCurves.TateModule.PrimaryDeterminant
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# `ρ_{E,ℓ} : G → GL₂(ℤ_[ℓ])` is continuous, at an arbitrary prime

`EllipticCurves.TateModule.PrimaryMatrixRep` builds the matrix form `galoisRepMatrix b` of the
`ℓ`-adic Galois representation out of a basis `b` of `T_ℓE`, as a homomorphism of abstract groups;
`EllipticCurves.TateModule.Continuity` proves that the *abstract* representation
`galoisRep ℓ : G →* Aut(T_ℓE)` is continuous for the profinite topology on `T_ℓE`. Neither says
anything about `GL₂(ℤ_[ℓ])` with its `ℓ`-adic topology, which is what "the `ℓ`-adic
representation" classically means. This file closes that gap, at **any** prime.

## The obstruction that was not there

Three files each excluded this as a stretch goal with the same stated reason: that the
compact-bijection-is-a-homeomorphism argument is circular, because it needs the continuity of
`b.repr` that one is trying to prove, and that one would therefore first have to construct a basis
compatible with the level filtration.

The argument is not circular; it simply runs in the other direction. The map
`b.equivFun.symm : ℤ_[ℓ]² → T_ℓE` is continuous **for free** — it is `x ↦ ∑ i, x i • b i`, and
`T_ℓE` is already known to be a topological `ℤ_[ℓ]`-module
(`tateModule.instContinuousSMulPadicInt`). Its *source* `Fin 2 → ℤ_[ℓ]` is compact
(`PadicInt.compactSpace`), and its *target* `T_ℓE` is Hausdorff (`tateModule.t2Space`). A
continuous bijection from a compact space to a Hausdorff space is a homeomorphism, so `b.equivFun`
is continuous by inversion. The compactness consumed is that of `ℤ_[ℓ]²`, not that of `T_ℓE`, and
no level-compatible basis is needed: **any** basis works.

## What this file is, and why it is `ℓ`-generic

This is the **extraction** of `EllipticCurves.TateModule.MatrixContinuity` to an arbitrary prime,
and it is the fifth link in a chain that has now worked five times:
`EllipticCurves.Torsion.PrimaryBasis` → `EllipticCurves.TateModule.PrimaryFree` →
`EllipticCurves.TateModule.PrimaryMatrixRep` → `EllipticCurves.TateModule.PrimaryDeterminant` →
here.

⚠️ **Thirteen of the sixteen statements below mention the prime only through `ℤ_[ℓ]`.** The
coordinate homeomorphism, its packaged linear form, the entrywise continuity of the matrix and the
two invariants-through-a-basis statements are all arguments about a basis one was *handed*, and
have no arithmetic content whatsoever. Only the three that produce a basis for themselves consume
anything prime-specific, and what they consume is stated here as a **hypothesis**:

```
(h : Nonempty ((W'⁄F).tateModule ℓ ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ]))
```

That is the same hypothesis `exists_galoisRepMatrix_of_nonempty`
(`EllipticCurves.TateModule.PrimaryMatrixRep`) and `galoisTrace_one_of_nonempty`
(`EllipticCurves.TateModule.PrimaryDeterminant`) take — the fourth extraction in a row to land on
that slot — and exactly what `nonempty_tateModuleEquivProd_of_card`
(`EllipticCurves.TateModule.PrimaryFree`) produces: `nonempty_tateModuleEquivProd` at `ℓ = 2` and
`nonempty_tateModuleEquivProd_three` at `ℓ = 3`.

⚠️ **This file supplies no `Nonempty (T_ℓE ≃ₗ ℤ_[ℓ]²)` at any prime**, so on its own it proves
nothing non-degenerate about any curve. The instances are
`EllipticCurves.TateModule.MatrixContinuity` (`ℓ = 2`) and
`EllipticCurves.TateModule.MatrixContinuityThree` (`ℓ = 3`); at `ℓ ≥ 5` there is nothing to
instantiate with — see Scope.

## What is proved

* `tateModule.coordHomeomorph` — `T_ℓE ≃ₜ (Fin 2 → ℤ_[ℓ])`, and
  `tateModule.coordContinuousLinearEquiv` — the same map as a `ℤ_[ℓ]`-linear homeomorphism. This is
  the substance: *the profinite topology on `T_ℓE` is the `ℓ`-adic topology of a free
  `ℤ_[ℓ]`-module of rank `2`*. Everything else is a corollary.
* `continuous_galoisRepMatrix` — `ρ_{E,ℓ} : G →* GL₂(ℤ_[ℓ])` is continuous, for the Krull topology
  on `G` and the topology `GL₂(ℤ_[ℓ])` inherits from `ℤ_[ℓ]` through
  `Units.instTopologicalSpaceUnits`.
* `continuous_galoisDet_of_basis`, `continuous_galoisTrace_of_basis` — the invariants of
  `EllipticCurves.TateModule.PrimaryDeterminant` are continuous.
* `exists_continuous_galoisRepMatrix_of_nonempty` — the choice-free capstone, the continuous
  refinement of `exists_galoisRepMatrix_of_nonempty`.

## Where the `[Algebra.IsIntegral S F]` split falls, and why it is not the same split

⚠️ **The file splits twice, at two different places, and the two splits do not coincide.** The
first nine declarations — everything about `coordHomeomorph` — need **no**
`[Algebra.IsIntegral S F]` and **no** `Nonempty` hypothesis: they are statements about the
`ℤ_[ℓ]`-module structure of `T_ℓE` alone, and their only topological input
`tateModule.instContinuousSMulPadicInt` (`EllipticCurves.TateModule.Continuity`) does not carry
`[Algebra.IsIntegral S F]` **in its signature**, because its term uses none of it. The remaining
seven need `[Algebra.IsIntegral S F]`, because every one of them goes through
`tateModule.continuous_galois_smul`, a `theorem` whose signature does carry it — that is the
*Galois* input, and it is what makes the orbit maps continuous. Of those seven, only the last three
additionally need the `Nonempty` hypothesis, and they need it for a different reason: to obtain a
basis rather than be handed one.

⚠️ **The `omit` written ahead of `tateModule.instContinuousSMulPadicInt` is not the reason, and
this section used to say that it was** — it read *"their only topological input
`tateModule.instContinuousSMulPadicInt` carries an explicit `omit [Algebra.IsIntegral S F]` in
`EllipticCurves.TateModule.Continuity`"*. That declaration is an `instance`, and on
`leanprover/lean4:v4.32.0` an `omit … in` is read only for a `theorem` (`Lean.Elab.MutualDef`,
`withHeaderSecVars`); ahead of a `def`, an `abbrev` or an `instance` it is accepted and discarded,
with no error and no `unusedSectionVars` report. The conclusion is unchanged and was never in
doubt; only its evidence was void. ⚠️ **A claim about a signature is a claim about what the
elaborator prints** — check it with `#check @`, not by reading the `omit` written ahead of the
declaration. `EllipticCurves.TateModule.PrimaryImageProfinite`'s `## Hypotheses` section records
the one declaration in this development whose inert `omit` did leave a binder in the signature.

## Non-degeneracy: the codomain is not discrete

⚠️ **`Continuous ρ` into a discrete codomain is free**, and that is exactly the situation of
`continuous_galoisRepMod`, where `E[n]` carries the discrete topology and continuity is only
levelwise local constancy. It is not the situation here, and the two certificates at the end of
this file say so: `PadicInt.not_discreteTopology` and
`Matrix.GeneralLinearGroup.not_discreteTopology_padicInt`. ⚠️ **Both are stated at an arbitrary
prime `p` and always were**, so neither has or needs a per-prime twin: the instantiating files cite
them rather than restate them.

⚠️ These certificates are about the *codomain*, not about the curve. What rules out the degenerate
reading on the *source* side — that `T_ℓE` is the zero module, over which every statement below is
true and worthless — is `Nonempty (T_ℓE ≃ₗ ℤ_[ℓ]²)`, and this file takes it as a hypothesis rather
than proving it. The instantiating files close that separately, with `Infinite (T_ℓE)`.

## Scope

* **No rank input.** See above: this file states continuity and takes rank two as a hypothesis
  exactly where a basis has to be produced.
* **The identification of `galoisDet` with the cyclotomic character is not proved here**, at any
  prime, and continuity does not bring it closer. See
  `EllipticCurves.TateModule.PrimaryDeterminant`'s Scope; ⚠️ the short version is that it needs the
  Weil pairing at **every** level `E[ℓ^k]`, and the mod-`n` identity is a different statement about
  a different object.
* **Openness and closedness of the image are not here.** ⚠️ **The clause this bullet used to
  carry has been paid for one of its two files** — it read *"`EllipticCurves.TateModule.Image` and
  `EllipticCurves.TateModule.ImageProfinite` … are still `ℓ = 2` only … Nothing gates their `ℓ = 3`
  layer; it has simply not been written"*. Closedness of the image is now stated at an arbitrary
  prime in `EllipticCurves.TateModule.PrimaryImage`, over *this* file, with instantiations at
  `ℓ = 2` (`EllipticCurves.TateModule.Image`) and `ℓ = 3`
  (`EllipticCurves.TateModule.ImageThree`). ⚠️ **The clause that scoped that repair to one of the
  two files has since been paid too**: it read *"`EllipticCurves.TateModule.ImageProfinite` — the
  `ProfiniteGrp` packaging — is still `ℓ = 2` only, still ungated, and a separate follow-up"*. The
  packaging is now stated at an arbitrary prime in
  `EllipticCurves.TateModule.PrimaryImageProfinite`, with instantiations at `ℓ = 2` and `ℓ = 3`
  (`EllipticCurves.TateModule.ImageProfiniteThree`).
  ⚠️ **Openness is a different matter and is not a follow-up at all**: it is Serre's theorem, it is
  *false* for curves with complex multiplication, and nothing here approaches it.
* **Local constancy is false**, not merely unproved — see `EllipticCurves.TateModule.OpenKernel`.
* ⚠️ **`ℓ ≥ 5` gains nothing from this file being generic.** Its hypothesis
  `Nonempty (T_ℓE ≃ₗ ℤ_[ℓ]²)` is gated at `ℓ ≥ 5` on `[ℓ]`-surjectivity and `#E[ℓ^k]`, both of
  which need the general coordinate formula `x(nP) = Φₙ/ΨSqₙ`, i.e. the `ωₙ` crux. What being
  generic buys is that when that gate is paid, the `ℓ = 5` file is a list of instantiations and no
  argument has to be written a third time.

## Using this file

Everything is stated for a base change `W'⁄F` of a curve `W' : Affine S` rather than for a bare
`W : Affine F`, matching the representation section of
`EllipticCurves.TateModule.PrimaryMatrixRep`. This is forced:
`tateModule.instContinuousSMulPadicInt` and `tateModule.continuous_galois_smul` are themselves
stated about `(W'⁄F).tateModule ℓ`, and instance search will not unify a bare `W` with
`?W'.baseChange F`.

⚠️ **Nothing in this file carries `[IsAlgClosed F]` or `[(W'⁄F).IsElliptic]`.** Those instances are
how the *instantiating* files obtain the `Nonempty` hypothesis, and this file is handed the
conclusion. `Fact ℓ.Prime` is what `ℤ_[ℓ]` and `galoisRep ℓ` require; Mathlib supplies it globally
at `2` and at `3`.

## Main definitions

* `WeierstrassCurve.Affine.tateModule.coordHomeomorph` : `T_ℓE ≃ₜ (Fin 2 → ℤ_[ℓ])`.
* `WeierstrassCurve.Affine.tateModule.coordContinuousLinearEquiv` : the same map, `ℤ_[ℓ]`-linearly.

## Main statements

* `WeierstrassCurve.Affine.continuous_galoisRepMatrix` : `ρ_{E,ℓ} : G →* GL₂(ℤ_[ℓ])` is continuous.
* `WeierstrassCurve.Affine.continuous_galoisDet_of_basis`,
  `WeierstrassCurve.Affine.continuous_galoisTrace_of_basis` : the invariants are continuous.
* `WeierstrassCurve.Affine.exists_continuous_galoisRepMatrix_of_nonempty` : the choice-free
  capstone.
* `Matrix.GeneralLinearGroup.not_discreteTopology_padicInt` : the codomain is not discrete, so the
  statements above are not formalities.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open Matrix

open scoped WeierstrassCurve.Affine.ProfiniteTopology

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
variable {ℓ : ℕ} [Fact ℓ.Prime]

namespace tateModule

variable (b : Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ))

/-! ### The coordinate homeomorphism `T_ℓE ≃ₜ ℤ_[ℓ]²` -/

/-- **Reading a coordinate vector back into `T_ℓE` is continuous.** This is the free half of the
coordinate homeomorphism: `b.equivFun.symm x = ∑ i, x i • b i`, and `T_ℓE` is a topological
`ℤ_[ℓ]`-module. -/
theorem continuous_equivFun_symm :
    Continuous (b.equivFun.symm : (Fin 2 → ℤ_[ℓ]) → (W'⁄F).tateModule ℓ) := by
  have h : (b.equivFun.symm : (Fin 2 → ℤ_[ℓ]) → (W'⁄F).tateModule ℓ)
      = fun x => ∑ i, x i • b i := funext fun x => b.equivFun_symm_apply x
  rw [h]
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const

/-- **The profinite topology on `T_ℓE` is the `ℓ`-adic topology of `ℤ_[ℓ]²`.**

`continuous_equivFun_symm` is a continuous bijection out of the compact space `Fin 2 → ℤ_[ℓ]`
(`PadicInt.compactSpace` and `Pi.compactSpace`) into the Hausdorff space `T_ℓE`
(`tateModule.t2Space`), hence a homeomorphism.

This is where the supposed circularity of the compact-to-Hausdorff argument dissolves: the
compactness used is that of the *coordinate space*, which Mathlib supplies, so no basis compatible
with the level filtration has to be constructed first. -/
noncomputable def coordHomeomorph : (W'⁄F).tateModule ℓ ≃ₜ (Fin 2 → ℤ_[ℓ]) :=
  (Continuous.homeoOfEquivCompactToT2 (f := b.equivFun.symm.toEquiv)
    (continuous_equivFun_symm b)).symm

@[simp]
theorem coe_coordHomeomorph :
    (coordHomeomorph b : (W'⁄F).tateModule ℓ → (Fin 2 → ℤ_[ℓ])) = b.equivFun := rfl

@[simp]
theorem coe_coordHomeomorph_symm :
    ((coordHomeomorph b).symm : (Fin 2 → ℤ_[ℓ]) → (W'⁄F).tateModule ℓ) = b.equivFun.symm := rfl

/-- **Taking coordinates is continuous.** The half that needed the compactness argument. -/
theorem continuous_equivFun :
    Continuous (b.equivFun : (W'⁄F).tateModule ℓ → (Fin 2 → ℤ_[ℓ])) :=
  (coordHomeomorph b).continuous

/-- Each coordinate function `f ↦ b.repr f i` is continuous. This is the form the matrix entries
are read through. -/
theorem continuous_repr_apply (i : Fin 2) :
    Continuous fun f : (W'⁄F).tateModule ℓ => b.repr f i :=
  (continuous_apply i).comp (continuous_equivFun b)

/-- **`T_ℓE` is topologically a free `ℤ_[ℓ]`-module of rank `2`**: the coordinate isomorphism
attached to a basis is a homeomorphism, so it is an isomorphism of topological `ℤ_[ℓ]`-modules.

This is the packaged form of `coordHomeomorph`, and the form a consumer wants: it carries the
`ℤ_[ℓ]`-linearity that `Homeomorph` alone does not. -/
noncomputable def coordContinuousLinearEquiv :
    (W'⁄F).tateModule ℓ ≃L[ℤ_[ℓ]] (Fin 2 → ℤ_[ℓ]) where
  toLinearEquiv := b.equivFun
  continuous_toFun := continuous_equivFun b
  continuous_invFun := continuous_equivFun_symm b

@[simp]
theorem coe_coordContinuousLinearEquiv :
    (coordContinuousLinearEquiv b : (W'⁄F).tateModule ℓ → (Fin 2 → ℤ_[ℓ])) = b.equivFun := rfl

@[simp]
theorem coordContinuousLinearEquiv_toLinearEquiv :
    (coordContinuousLinearEquiv b).toLinearEquiv = b.equivFun := rfl

end tateModule

/-! ### Continuity of the matrix representation

⚠️ `[Algebra.IsIntegral S F]` enters here and not above: from this point on every proof goes
through `tateModule.continuous_galois_smul`, which is the one input of
`EllipticCurves.TateModule.Continuity` used below that does **not** carry an
`omit [Algebra.IsIntegral S F]`. -/

variable [Algebra.IsIntegral S F]
variable (b : Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ))

/-- **The matrix of `ρ_{E,ℓ}(σ)` depends continuously on `σ`.**

Entrywise: `(ρ σ) i j = b.repr (σ • b j) i` is the composite of the continuous orbit map
`σ ↦ σ • b j` with the continuous coordinate function. -/
theorem continuous_galoisRepMatrix_coe :
    Continuous fun σ : F ≃ₐ[S] F =>
      (galoisRepMatrix b σ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) := by
  refine continuous_matrix fun i j => ?_
  simp only [galoisRepMatrix_apply_coe]
  exact (tateModule.continuous_repr_apply b i).comp (tateModule.continuous_galois_smul ℓ (b j))

/-- **`ρ_{E,ℓ} : G →* GL₂(ℤ_[ℓ])` is continuous**, for the Krull topology on `G` and the `ℓ`-adic
topology on `GL₂(ℤ_[ℓ])`.

This is the classical statement that `galoisRepMatrix` was one step short of. `GL` carries the
topology induced from `Matrix × Matrix` by `u ↦ (u, u⁻¹)`, so both the matrix and its inverse must
vary continuously; the inverse costs nothing, since `↑(ρ σ)⁻¹ = ↑(ρ σ⁻¹)` and inversion is
continuous in the topological group `G`. -/
theorem continuous_galoisRepMatrix : Continuous (galoisRepMatrix b) := by
  rw [Units.continuous_iff]
  refine ⟨continuous_galoisRepMatrix_coe b, ?_⟩
  simp_rw [← map_inv]
  exact (continuous_galoisRepMatrix_coe b).comp continuous_inv

/-! ### The invariants are continuous -/

/-- **The determinant character `det ρ_{E,ℓ} : G →* ℤ_[ℓ]ˣ` is continuous.**

`galoisDet` is basis-free, but its continuity is proved through a basis, which is why one is taken
as an argument; `continuous_galoisDet_of_nonempty` removes it. -/
theorem continuous_galoisDet_of_basis
    (b : Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ)) :
    Continuous (galoisDet (W' := W') (F := F) (ℓ := ℓ)) := by
  rw [Units.continuous_iff]
  constructor
  · simp only [Function.comp_def, coe_galoisDet b]
    exact (continuous_galoisRepMatrix_coe b).matrix_det
  · simp_rw [← map_inv, coe_galoisDet b]
    exact ((continuous_galoisRepMatrix_coe b).comp continuous_inv).matrix_det

/-- **The trace `tr ρ_{E,ℓ} : G → ℤ_[ℓ]` is continuous.** Unlike the determinant this is not a
homomorphism, so there is no unit-topology bookkeeping: it is the matrix trace of a continuously
varying matrix. -/
theorem continuous_galoisTrace_of_basis
    (b : Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ)) :
    Continuous (galoisTrace (W' := W') (F := F) (ℓ := ℓ)) := by
  have h : (galoisTrace (W' := W') (F := F) (ℓ := ℓ))
      = fun σ => (galoisRepMatrix b σ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]).trace :=
    funext fun σ => (trace_galoisRepMatrix b σ).symm
  rw [h]
  exact (continuous_galoisRepMatrix_coe b).matrix_trace

/-! ### The basis-free layer and the capstone

The three statements below are the only ones in this file that take a hypothesis about the curve,
and it is the same one throughout: `Nonempty (T_ℓE ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])`. ⚠️ The thirteen above
take a *basis*, which is an argument and not a hypothesis, and the two `_root_` certificates at the
end take a prime. ⚠️ They need it for a reason
unrelated to topology — to *produce* a basis rather than be handed one — so it is not the
non-degeneracy of the codomain, which is settled unconditionally at the end of this file. -/

/-- `det ρ_{E,ℓ}` is continuous, with no basis supplied: a basis exists as soon as `T_ℓE` is
`ℤ_[ℓ]`-linearly `ℤ_[ℓ]²`, and continuity is a `Prop`, so the choice can be discharged. -/
theorem continuous_galoisDet_of_nonempty
    (h : Nonempty ((W'⁄F).tateModule ℓ ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])) :
    Continuous (galoisDet (W' := W') (F := F) (ℓ := ℓ)) := by
  obtain ⟨b⟩ := tateModule.nonempty_basis_tateModule_of_nonempty (W := W'⁄F) h
  exact continuous_galoisDet_of_basis b

/-- `tr ρ_{E,ℓ}` is continuous, with no basis supplied. -/
theorem continuous_galoisTrace_of_nonempty
    (h : Nonempty ((W'⁄F).tateModule ℓ ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])) :
    Continuous (galoisTrace (W' := W') (F := F) (ℓ := ℓ)) := by
  obtain ⟨b⟩ := tateModule.nonempty_basis_tateModule_of_nonempty (W := W'⁄F) h
  exact continuous_galoisTrace_of_basis b

/-- **`ρ_{E,ℓ}` is a continuous `ℓ`-adic matrix representation.**

The continuous refinement of `exists_galoisRepMatrix_of_nonempty`: there are a basis of `T_ℓE` and
a **continuous** homomorphism `ρ : G →* GL₂(ℤ_[ℓ])` whose matrices compute the Galois action on
coordinate vectors.

The compatibility clause is load-bearing. `∃ ρ, Continuous ρ` alone is witnessed by the trivial
homomorphism and would mention neither the curve nor its Tate module; it is the clause that ties
`ρ` to `σ • ·` on `T_ℓE`.

⚠️ **Deletion test**, measured on this file as committed. Deleting the hypothesis `h` from the
statement and replacing `obtain ⟨b⟩ := tateModule.nonempty_basis_tateModule_of_nonempty
(W := W'⁄F) h` by `obtain ⟨b⟩ : Nonempty (Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ)) := ?_`
leaves, copy-paste:

```
error: don't know how to synthesize placeholder
context:
S : Type u_1
F : Type u_2
inst✝⁵ : Field S
inst✝⁴ : Field F
inst✝³ : DecidableEq F
inst✝² : Algebra S F
W' : Affine S
ℓ : ℕ
inst✝¹ : Fact (Nat.Prime ℓ)
inst✝ : Algebra.IsIntegral S F
⊢ Nonempty (Module.Basis (Fin 2) ℤ_[ℓ] ↥((W'⁄F).tateModule ℓ))
```

⚠️ One mechanical change accompanies the deletion and it adds no information: `obtain ⟨b⟩ := …`
becomes `obtain ⟨b⟩ : Nonempty … := ?_`, so that a hole is legal where the hypothesis was, and the
type must be written out rather than left as `_` since nothing else in the goal determines it. ⚠️
Unlike the deletion tests of `EllipticCurves.TateModule.PrimaryDeterminant` and
`EllipticCurves.TateModule.PrimaryMatrixRep` there is **no knock-on**: nothing below consumes this
theorem.

⚠️ The residual is a **goal** and not a type mismatch, and **nothing left in the context proves
it** — with `h` gone the context has no curve-theoretic content at all. That is the point: without
rank two there is no basis, hence no matrix, hence nothing whose continuity could be asserted, and
`Continuous ρ` for the trivial `ρ` is what the statement would collapse to. -/
theorem exists_continuous_galoisRepMatrix_of_nonempty
    (h : Nonempty ((W'⁄F).tateModule ℓ ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])) :
    ∃ (b : Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ))
      (ρ : (F ≃ₐ[S] F) →* GL (Fin 2) ℤ_[ℓ]), Continuous ρ ∧
        ∀ (σ : F ≃ₐ[S] F) (f : (W'⁄F).tateModule ℓ),
          ⇑(b.repr (σ • f)) = (ρ σ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) *ᵥ ⇑(b.repr f) := by
  obtain ⟨b⟩ := tateModule.nonempty_basis_tateModule_of_nonempty (W := W'⁄F) h
  exact ⟨b, galoisRepMatrix b, continuous_galoisRepMatrix b, galoisRepMatrix_mulVec b⟩

end WeierstrassCurve.Affine

/-! ### The codomain is not discrete

Continuity into a discrete space is no constraint at all, and that is precisely the situation of
`continuous_galoisRepMod`, whose codomain `E[n]` is discrete. The results above are not of that
kind, and this section is the certificate.

⚠️ **Both statements are already stated at an arbitrary prime `p`**, so they have no per-prime
twins and need none: `EllipticCurves.TateModule.MatrixContinuity` and
`EllipticCurves.TateModule.MatrixContinuityThree` cite them rather than restate them. They are
`_root_`-level facts about `ℤ_[p]` and `GL₂(ℤ_[p])` and mention no curve. -/

/-- `ℤ_[p]` is not discrete: it is compact and infinite. -/
theorem PadicInt.not_discreteTopology (p : ℕ) [Fact p.Prime] :
    ¬ DiscreteTopology ℤ_[p] := fun h =>
  @not_finite ℤ_[p] _ (@finite_of_compact_of_discrete _ _ _ h)

/-- **`GL₂(ℤ_[p])` is not discrete.** The unipotent line `x ↦ !![1, x; 0, 1]` is a continuous
injection of `ℤ_[p]` into it, so a discrete `GL₂` would force `{0}` open in `ℤ_[p]` and hence — the
latter being a topological additive group — `ℤ_[p]` itself discrete.

This is what makes `WeierstrassCurve.Affine.continuous_galoisRepMatrix` a statement rather than a
formality. -/
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
