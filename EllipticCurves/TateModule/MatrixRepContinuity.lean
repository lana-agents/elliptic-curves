/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.Continuity
import EllipticCurves.TateModule.MatrixRep
import EllipticCurves.TateModule.Profinite
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Instances.Matrix

/-!
# `ρ_{E,2} : G → GL₂(ℤ_[2])` is continuous for the `2`-adic topology

`EllipticCurves.TateModule.Continuity` proves that the `ℓ`-adic representation
`galoisRep ℓ : G →* (T_ℓE ≃ₗ[ℤ_[ℓ]] T_ℓE)` is continuous for the topology of *pointwise
convergence* on `T_ℓE → T_ℓE`. That is a genuine statement, but it is not the classical one. The
classical statement is about the matrix form

```
galoisRepMatrixTwo b : G →* GL (Fin 2) ℤ_[2]
```

of `EllipticCurves.TateModule.MatrixRep`, with `GL₂(ℤ_[2])` carrying its own `2`-adic topology —
the subspace topology from `ℤ_[2]^{2×2} × ℤ_[2]^{2×2}` under `u ↦ (u, u⁻¹)`. This file proves it:

```
continuous_galoisRepMatrixTwo : Continuous ⇑(galoisRepMatrixTwo b)
```

for any basis `b` whose coordinate map `b.repr` is continuous, together with the fact that the
basis this development actually constructs *is* such a basis.

## The hinge: the compatible basis is a homeomorphism, not merely a linear equivalence

`T₂E` has no canonical basis, and continuity of `galoisRepMatrixTwo b` is a statement about `b` as
much as about `E`: a `ℤ_[2]`-linear automorphism of `ℤ_[2]²` need not be continuous unless one
knows the module topology is the `2`-adic one, and `T₂E` carries its topology from the inverse
limit, not from a basis. So the coordinate map has to be *proved* continuous for the basis in hand.

Three earlier issues on this front (#592, #597, #598) each deferred this with the same reason:

> compactness does not give it — "a continuous bijection from a compact space is a homeomorphism"
> needs exactly the continuity one is trying to prove.

That is correct for an *arbitrary* basis and wrong for the basis this development builds, because
the argument is applied in the wrong direction. What has to be continuous first is not `b.repr` but
its inverse

```
Φ = padicPairHom hgen hP hQ : ℤ_[2] × ℤ_[2] →ₗ[ℤ_[2]] T₂E,
Φ (a, b) k = (toZModPow k a).val • P k + (toZModPow k b).val • Q k,
```

and `Φ` is continuous *directly*: level `k` lands in the discrete space `E(F)` and factors through
`toZModPow k`, which is locally constant (`PadicInt.toZModPow_eventuallyEq`, proved in
`EllipticCurves.TateModule.Continuity` for precisely this shape). No circularity: nothing about
`b.repr` is used.

The compact-to-Hausdorff argument then runs in the direction where it is available. The *source*
`ℤ_[2] × ℤ_[2]` is compact — that is `PadicInt.compactSpace`, from Mathlib, not the compactness of
`T₂E` proved in `EllipticCurves.TateModule.Profinite` — and the *target* `T₂E` is Hausdorff. A
continuous bijection from a compact space to a Hausdorff space is a homeomorphism, so `Φ⁻¹`, and
with it `b.repr`, is continuous for free.

The resulting statement is worth more than the continuity it was extracted for:

```
padicPairContinuousLinearEquiv : (ℤ_[2] × ℤ_[2]) ≃L[ℤ_[2]] T₂E
```

**the `2`-adic topology on `T₂E` is the product topology on `ℤ_[2]²`**, as an isomorphism of
topological `ℤ_[2]`-modules. This is to the coordinates what
`EllipticCurves.TateModule.Profinite`'s `isClosedEmbedding_levelFamily` is to the levels: it turns
"`T₂E` carries the `2`-adic topology" from a name into a theorem.

## Why the basis hypothesis is carried rather than baked in

`continuous_galoisRepMatrixTwo` takes `hb : Continuous fun f => ⇑(b.repr f)` as a hypothesis, in
the same style as the `Finite (E[n])` hypothesis in `EllipticCurves.TateModule.OpenKernel`. Two
bases of `T₂E` differ by a `ℤ_[2]`-linear automorphism, and the two matrix representations differ
by conjugation by the corresponding element of `GL₂(ℤ_[2])`; conjugation is a homeomorphism of
`GL₂(ℤ_[2])`, so *continuity of `galoisRepMatrixTwo b` does not in fact depend on `b`* once one
basis with continuous `repr` is known to exist. That remark is not formalised here — what is
formalised is the hypothesis-carrying version plus the witness that the hypothesis is satisfiable
(`continuous_repr_tateModuleBasisTwo`), which is what downstream files need.

## Non-degeneracy

Continuity is vacuous into an indiscrete codomain and trivial out of a discrete source, so both are
excluded:

* the codomain is Hausdorff and nontrivial — `t2Space_generalLinearGroupTwo` and
  `nontrivial_generalLinearGroupTwo` below;
* the source is **not** discrete — `not_discreteTopology_tateModule_two` from
  `EllipticCurves.TateModule.Profinite`. Transported across the homeomorphism this also says
  `ℤ_[2] × ℤ_[2]` is not discrete, so `Φ` is a homeomorphism between two genuinely non-discrete
  compact groups rather than a statement about discrete spaces.

As in `EllipticCurves.TateModule.OpenKernel`, every statement about `G` here remains true when
`G = F ≃ₐ[S] F` is trivial, and no theorem about `G` alone can exclude that — it is a fact about
the extension `F / S`, not about the curve. The certificate offered instead is the one above, which
is about the curve: the topologies at both ends are non-discrete and `T₂E ≃ ℤ_[2]²` as topological
modules.

## Scope

`ℓ = 2` only. The coherent system of generating pairs comes from
`EllipticCurves.Torsion.TwoPrimaryBasis.exists_compatible_basis`, which is `2`-primary; odd `ℓ`
waits on finiteness of `E[n]` (#252) and hence on `x(nP) = Φₙ/ΨSqₙ` (#251). Nothing here bears on
`det ρ_{E,2}` and the cyclotomic character (Weil-pairing gated), nor on the image of `ρ_{E,2}`:
`G` is not known compact, so no openness statement about the image is available.

## Main statements

* `WeierstrassCurve.Affine.tateModule.continuous_padicPairHom` : `Φ : ℤ_[2] × ℤ_[2] → T₂E` is
  continuous — the only continuity proved from scratch here.
* `WeierstrassCurve.Affine.tateModule.padicPairContinuousLinearEquiv` : `ℤ_[2] × ℤ_[2] ≃L[ℤ_[2]]
  T₂E`, and `nonempty_continuousLinearEquiv_tateModule_two` for the choice-free form.
* `WeierstrassCurve.Affine.tateModule.continuous_repr_tateModuleBasisTwo` : the coordinate map of
  the basis attached to a continuous equivalence is continuous.
* `WeierstrassCurve.Affine.continuous_galoisRepMatrixTwo` : `ρ_{E,2} : G → GL₂(ℤ_[2])` is
  continuous, given a basis with continuous coordinate map.
* `WeierstrassCurve.Affine.exists_continuous_galoisRepMatrixTwo` : such a basis exists, so the
  `2`-adic representation exists as a continuous representation computing the Galois action.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open Matrix PadicInt

open scoped WeierstrassCurve.Affine.ProfiniteTopology

namespace WeierstrassCurve.Affine

namespace tateModule

/-! ### `Φ : ℤ_[2] × ℤ_[2] → T₂E` is continuous -/

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} {P Q : ℕ → W.Point}

/-- **The coordinate map `Φ` is continuous.** At level `k` the value
`(toZModPow k a).val • P k + (toZModPow k b).val • Q k` lands in the discrete space `E(F)` and
depends on `(a, b)` only through the residues `toZModPow k`, which are locally constant. This is
the one continuity statement in the file that is proved from scratch; everything else is formal
consequence. -/
theorem continuous_padicPairHom
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (2 ^ k))
    (hP : ∀ k, 2 • P (k + 1) = P k) (hQ : ∀ k, 2 • Q (k + 1) = Q k) :
    Continuous (padicPairHom hgen hP hQ) := by
  rw [continuous_induced_rng]
  refine continuous_pi fun k => continuous_iff_continuousAt.2 fun ab => ?_
  rw [ContinuousAt, nhds_discrete W.Point, Filter.tendsto_pure]
  filter_upwards [(continuous_fst.tendsto ab).eventually (toZModPow_eventuallyEq k ab.1),
    (continuous_snd.tendsto ab).eventually (toZModPow_eventuallyEq k ab.2)] with x hx₁ hx₂
  change (toZModPow k x.1).val • P k + (toZModPow k x.2).val • Q k
    = (toZModPow k ab.1).val • P k + (toZModPow k ab.2).val • Q k
  rw [hx₁, hx₂]

variable [IsAlgClosed F] [W.IsElliptic]

/-- `Φ`, read as the linear equivalence `padicPairEquiv`, is continuous. -/
theorem continuous_padicPairEquiv (h2 : (2 : F) ≠ 0)
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (2 ^ k))
    (hP : ∀ k, 2 • P (k + 1) = P k) (hQ : ∀ k, 2 • Q (k + 1) = Q k) :
    Continuous (padicPairEquiv h2 hgen hP hQ) :=
  continuous_padicPairHom hgen hP hQ

/-! ### `T₂E ≃L[ℤ_[2]] ℤ_[2] × ℤ_[2]` : the topology *is* the `2`-adic one -/

/-- **The `2`-adic topology on `T₂E` is the product topology on `ℤ_[2]²`**, as an isomorphism of
topological `ℤ_[2]`-modules.

The inverse is continuous by the compact-to-Hausdorff principle applied in the only direction in
which it is available: the *source* `ℤ_[2] × ℤ_[2]` is compact (`PadicInt.compactSpace`) and the
*target* `T₂E` is Hausdorff, so the continuous bijection `Φ` is a homeomorphism. Compactness of
`T₂E` itself (`EllipticCurves.TateModule.Profinite`) is not what is used, and would not suffice. -/
noncomputable def padicPairContinuousLinearEquiv (h2 : (2 : F) ≠ 0)
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (2 ^ k))
    (hP : ∀ k, 2 • P (k + 1) = P k) (hQ : ∀ k, 2 • Q (k + 1) = Q k) :
    (ℤ_[2] × ℤ_[2]) ≃L[ℤ_[2]] W.tateModule 2 where
  __ := padicPairEquiv h2 hgen hP hQ
  continuous_toFun := continuous_padicPairEquiv h2 hgen hP hQ
  continuous_invFun :=
    ((continuous_padicPairEquiv h2 hgen hP hQ).homeoOfEquivCompactToT2
      (f := (padicPairEquiv h2 hgen hP hQ).toEquiv)).symm.continuous

@[simp]
theorem coe_padicPairContinuousLinearEquiv (h2 : (2 : F) ≠ 0)
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (2 ^ k))
    (hP : ∀ k, 2 • P (k + 1) = P k) (hQ : ∀ k, 2 • Q (k + 1) = Q k) :
    ⇑(padicPairContinuousLinearEquiv h2 hgen hP hQ) = ⇑(padicPairEquiv h2 hgen hP hQ) :=
  rfl

/-- The inverse coordinate map `T₂E → ℤ_[2] × ℤ_[2]` is continuous. This is the statement the
matrix representation needs. -/
theorem continuous_padicPairEquiv_symm (h2 : (2 : F) ≠ 0)
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (2 ^ k))
    (hP : ∀ k, 2 • P (k + 1) = P k) (hQ : ∀ k, 2 • Q (k + 1) = Q k) :
    Continuous (padicPairEquiv h2 hgen hP hQ).symm :=
  (padicPairContinuousLinearEquiv h2 hgen hP hQ).continuous_invFun

/-- **`T₂E` is isomorphic to `ℤ_[2]²` as a topological `ℤ_[2]`-module**, choice-freely. The
isomorphism itself depends on a coherent system of generating pairs of the `E[2^k]`; its existence
does not, exactly as for `nonempty_tateModuleEquivProd`, of which this is the topological
refinement. -/
theorem nonempty_continuousLinearEquiv_tateModule_two (h2 : (2 : F) ≠ 0) :
    Nonempty ((ℤ_[2] × ℤ_[2]) ≃L[ℤ_[2]] W.tateModule 2) := by
  obtain ⟨P, Q, hgen, hP, hQ⟩ := exists_compatible_basis (W := W) h2
  exact ⟨padicPairContinuousLinearEquiv h2 hgen hP hQ⟩

/-- **The identification is between non-discrete spaces**: given the topological isomorphism
`ℤ_[2] × ℤ_[2] ≃L[ℤ_[2]] T₂E`, non-discreteness of `T₂E`
(`not_discreteTopology_tateModule_two`) transports to the source.

This is a consistency check on the transport rather than new information about `ℤ_[2]`, and it is
recorded for exactly that reason: it certifies that `padicPairContinuousLinearEquiv` does not
collapse the topology at either end, so the continuity statements built on it are not statements
about discrete spaces. -/
theorem not_discreteTopology_padicPairProd (h2 : (2 : F) ≠ 0)
    (e : (ℤ_[2] × ℤ_[2]) ≃L[ℤ_[2]] W.tateModule 2) :
    ¬ DiscreteTopology (ℤ_[2] × ℤ_[2]) := fun _ =>
  not_discreteTopology_tateModule_two W h2 e.toHomeomorph.symm.isEmbedding.discreteTopology

/-! ### Continuity of the coordinate map of a basis -/

omit [IsAlgClosed F] [W.IsElliptic] in
/-- The coordinate map of the basis attached to a *continuous* linear equivalence
`T₂E ≃ₗ[ℤ_[2]] ℤ_[2] × ℤ_[2]` is continuous. The only content beyond `Basis.ofEquivFun_repr_apply`
is that `ℤ_[2] × ℤ_[2] ≃ (Fin 2 → ℤ_[2])` is continuous, which is `Fin.cases` on the index. -/
theorem continuous_repr_tateModuleBasisTwo (e : W.tateModule 2 ≃ₗ[ℤ_[2]] ℤ_[2] × ℤ_[2])
    (he : Continuous e) :
    Continuous fun f : W.tateModule 2 => ⇑((tateModuleBasisTwo e).repr f) := by
  refine continuous_pi fun i => ?_
  simp only [tateModuleBasisTwo, Module.Basis.ofEquivFun_repr_apply, LinearEquiv.trans_apply,
    LinearEquiv.finTwoArrow_symm_apply]
  fin_cases i
  · exact continuous_fst.comp he
  · exact continuous_snd.comp he

end tateModule

/-! ### `ρ_{E,2}` is continuous into `GL₂(ℤ_[2])` -/

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
variable [Algebra.IsIntegral S F]
variable (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2))

/-- **The matrix of `σ` depends continuously on `σ`**, given a basis with continuous coordinate
map.

The entry `(ρ σ) i j` is `b.repr (σ • b j) i` (`galoisRepMatrixTwo_apply_coe`), so it is the
composite of the continuous orbit map `σ ↦ σ • b j` with `b.repr` and a coordinate projection.
Nothing here yet says the map into `GL₂` is continuous — that needs the inverse too, which is
`continuous_galoisRepMatrixTwo`. -/
theorem continuous_coe_galoisRepMatrixTwo
    (hb : Continuous fun f : (W'⁄F).tateModule 2 => ⇑(b.repr f)) :
    Continuous fun σ : F ≃ₐ[S] F =>
      (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]) := by
  refine continuous_matrix fun i j => ?_
  simp only [galoisRepMatrixTwo_apply_coe]
  exact (continuous_apply i).comp (hb.comp (tateModule.continuous_galois_smul 2 (b j)))

/-- **`ρ_{E,2} : G → GL₂(ℤ_[2])` is continuous** for the Krull topology on `G` and the `2`-adic
topology on `GL₂(ℤ_[2])`, whenever the coordinate map of `b` is continuous.

Continuity *into a unit group* is not continuity of the underlying matrix alone: by
`Units.continuous_iff` the inverse has to be continuous as well. Here that costs nothing extra,
because `ρ` is a group homomorphism, so `(ρ σ)⁻¹ = ρ σ⁻¹` and inversion on `G` is continuous —
`G` is a topological group in the Krull topology. This is the same `simp_rw [Units.continuous_iff,
← map_inv]` idiom Mathlib uses for `Matrix.GeneralLinearGroup.continuous_det`. -/
theorem continuous_galoisRepMatrixTwo
    (hb : Continuous fun f : (W'⁄F).tateModule 2 => ⇑(b.repr f)) :
    Continuous (galoisRepMatrixTwo b) := by
  rw [Units.continuous_iff]
  refine ⟨continuous_coe_galoisRepMatrixTwo b hb, ?_⟩
  simp only [← map_inv]
  exact (continuous_coe_galoisRepMatrixTwo b hb).comp continuous_inv

/-- **The `2`-adic representation exists as a *continuous* representation.**

The compatibility clause is what stops the statement from being vacuous: `∃ ρ, Continuous ρ` alone
is witnessed by the trivial homomorphism and would not mention the curve. As in
`exists_galoisRepMatrixTwo`, both the basis and `ρ` depend on a choice of coherent system of
generating pairs of the `E[2^k]`, and two choices give representations differing by conjugation. -/
theorem exists_continuous_galoisRepMatrixTwo [IsAlgClosed F] [(W'⁄F).IsElliptic]
    (h2 : (2 : F) ≠ 0) :
    ∃ (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2))
      (ρ : (F ≃ₐ[S] F) →* GL (Fin 2) ℤ_[2]), Continuous ρ ∧
        ∀ (σ : F ≃ₐ[S] F) (f : (W'⁄F).tateModule 2),
          ⇑(b.repr (σ • f)) = (ρ σ : Matrix (Fin 2) (Fin 2) ℤ_[2]) *ᵥ ⇑(b.repr f) := by
  obtain ⟨P, Q, hgen, hP, hQ⟩ := exists_compatible_basis (W := W'⁄F) h2
  refine ⟨tateModule.tateModuleBasisTwo (tateModule.padicPairEquiv h2 hgen hP hQ).symm,
    galoisRepMatrixTwo _, ?_, galoisRepMatrixTwo_mulVec _⟩
  exact continuous_galoisRepMatrixTwo _
    (tateModule.continuous_repr_tateModuleBasisTwo _
      (tateModule.continuous_padicPairEquiv_symm h2 hgen hP hQ))

/-! ### Non-degeneracy of the codomain -/

/-- `GL₂(ℤ_[2])` is Hausdorff, so continuity into it is not vacuous. -/
theorem t2Space_generalLinearGroupTwo : T2Space (GL (Fin 2) ℤ_[2]) :=
  inferInstance

/-- `GL₂(ℤ_[2])` has more than one element, so a continuous homomorphism into it is not a statement
about a one-point space. Together with `t2Space_generalLinearGroupTwo` this rules out the
indiscrete reading of every continuity statement above. -/
theorem nontrivial_generalLinearGroupTwo : Nontrivial (GL (Fin 2) ℤ_[2]) := by
  refine ⟨-1, 1, fun h => ?_⟩
  have hentry := congrArg (fun u : GL (Fin 2) ℤ_[2] =>
    (u : Matrix (Fin 2) (Fin 2) ℤ_[2]) 0 0) h
  norm_num [Units.val_neg, Matrix.neg_apply, Matrix.one_apply_eq] at hentry

end WeierstrassCurve.Affine
