/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.Continuity
import EllipticCurves.TateModule.LevelStructure
import EllipticCurves.Torsion.TwoPrimary
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!
# `T_ℓ E` is profinite

`EllipticCurves.TateModule.Continuity` puts the inverse-limit topology on `T_ℓ E` — the subspace
topology it inherits from `ℕ → E(F)` with `E(F)` discrete — and proves that it is a Hausdorff,
totally disconnected topological group on which the Galois group acts continuously. It stops short
of **compactness**, and says so.

This file supplies the missing piece. It rests on two observations.

* `T_ℓ E` does not merely sit inside `ℕ → E(F)`, which is *not* compact because `E(F)` is infinite:
  it sits inside the much smaller product `∏_k E[ℓ^k]`, which **is** compact as soon as every level
  `E[ℓ^k]` is finite, and inside which `T_ℓ E` is cut out by the closed conditions
  `ℓ · g (k+1) = g k`.
* At `ℓ = 2` the finiteness of every level is **already available and unconditional**:
  `EllipticCurves.Torsion.TwoPrimary` proves `#E[2^k] = 4^k` from the tangent-line doubling
  shortcut, with no appeal to Ward's theorem, to the elliptic-net recurrence, or to the
  multiplication-by-`n` coordinate formula `x(nP) = Φₙ(x)/ΨSqₙ(x)`.

So `T_2 E` is an honest profinite abelian group, and `ρ_{E,2}` is a continuous representation of a
topological group *on a profinite module* rather than merely on a topological one.

## The topology is the inverse-limit topology — as a theorem

The deliverable that carries the mathematical content is not compactness but
`WeierstrassCurve.Affine.tateModule.isClosedEmbedding_levelFamily`: the level-family map

```
levelFamily : T_ℓ E →+ ∏ k, E[ℓ^k],    f ↦ (proj k f)_k
```

is a **closed topological embedding**, with range exactly the compatible families
(`range_levelFamily`). `EllipticCurves.TateModule.Continuity` asserts in prose that the subspace
topology inherited from `ℕ → E(F)` "is the `ℓ`-adic (inverse-limit) topology"; this is that
assertion made checkable. Compactness is then a two-line corollary of Tychonoff.

## Conditionality

* `isClosed_setOf_isCompatibleLevels`, `range_levelFamily`, `isEmbedding_levelFamily`,
  `isClosedEmbedding_levelFamily`, `isOpen_ker_proj` and `iInf_ker_proj` are **unconditional**:
  they hold for every `ℓ` and every Weierstrass curve, finite levels or not.
* `compactSpace` and `isCompact_coe` take the hypothesis `∀ k, Finite (W.torsion (ℓ ^ k))`.
* `compactSpace_two`, `not_discreteTopology_tateModule_two` and `profiniteAddGrpTwo` discharge that
  hypothesis **unconditionally at `ℓ = 2`** via `finite_torsion_two_pow`.

**This supersedes, at `ℓ = 2`, the "No compactness" paragraph in the module docstring of
`EllipticCurves.TateModule.Continuity`.** That paragraph says finiteness of `E[n]` "is not
available in this development"; it is available for `n = 2^k`, and has been since the `2`-primary
tower landed. For **odd** `ℓ` the paragraph still stands: `Finite (E[ℓ^k])` needs `#E[ℓ] ≤ ℓ²`,
which needs the coordinate formula, so the general-`ℓ` statements below are left conditional rather
than faked.

## Non-degeneracy

`CompactSpace` is free for the zero module, and `ProfiniteAddGrp.of` accepts it, so a file proving
`T_ℓ E` compact certifies nothing on its own. The discriminating statement is in the file:
`not_discreteTopology_tateModule_two`, i.e. `T_2 E` is compact **and infinite**
(`infinite_tateModule_two`), hence its topology is not the discrete one. A compact discrete space
is finite, so this single statement rules out both degenerate readings at once — the zero module,
and the possibility that "the profinite topology" is secretly discrete and every continuity theorem
about it vacuous.

## Main statements

* `WeierstrassCurve.Affine.tateModule.isClosedEmbedding_levelFamily` : `T_ℓ E ↪ ∏_k E[ℓ^k]` is a
  closed embedding — the topology on `T_ℓ E` *is* the inverse-limit topology.
* `WeierstrassCurve.Affine.tateModule.compactSpace` : `T_ℓ E` is compact when every level is finite.
* `WeierstrassCurve.Affine.tateModule.compactSpace_two` : `T_2 E` is compact, unconditionally.
* `WeierstrassCurve.Affine.tateModule.not_discreteTopology_tateModule_two` : `T_2 E` is not
  discrete.
* `WeierstrassCurve.Affine.tateModule.profiniteAddGrpTwo` : `T_2 E` as an object of
  `ProfiniteAddGrp`.
* `WeierstrassCurve.Affine.tateModule.isOpen_ker_proj`,
  `WeierstrassCurve.Affine.tateModule.iInf_ker_proj` : the level filtration is a filtration by open
  subgroups intersecting in `0`.

## Scope

Nothing here bears on **odd `ℓ`** beyond the conditional statements, on `T_ℓ E ≅ ℤ_ℓ²`, on
continuity of `ρ_{E,2}` into `GL₂(ℤ_[2])` **with its `2`-adic topology** (that needs a basis
compatible with the level filtration, and compactness of `T_2 E` does not supply it; it is proved
in `EllipticCurves.TateModule.MatrixRepContinuity`, from compactness of `ℤ_[2] × ℤ_[2]` instead),
on the image of `ρ_ℓ`, or on `det ρ_{E,2}` and the cyclotomic character.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open scoped WeierstrassCurve.Affine.ProfiniteTopology

namespace WeierstrassCurve.Affine

namespace tateModule

variable {F : Type*} [Field F] [DecidableEq F] (W : Affine F) (ℓ : ℕ)

/-! ### The compatible families inside the product of the levels -/

/-- The transition relations, read on a family of *level* points `g k ∈ E[ℓ^k]` rather than on a
family of points of `E(F)`. Compare `WeierstrassCurve.Affine.IsCompatibleFamily`, which additionally
has to record the torsion condition; here it is carried by the types. -/
def IsCompatibleLevels (g : ∀ k, W.torsion (ℓ ^ k)) : Prop :=
  ∀ k, ℓ • ((g (k + 1) : W.Point)) = (g k : W.Point)

/-- **The compatible families form a closed subset of `∏_k E[ℓ^k]`.** Each transition relation is
an equaliser of two continuous maps into `E(F)`, which is discrete and hence Hausdorff. This is the
only topological input to compactness. -/
theorem isClosed_setOf_isCompatibleLevels :
    IsClosed {g : ∀ k, W.torsion (ℓ ^ k) | IsCompatibleLevels W ℓ g} := by
  have hset : {g : ∀ k, W.torsion (ℓ ^ k) | IsCompatibleLevels W ℓ g}
      = ⋂ k : ℕ, {g : ∀ k, W.torsion (ℓ ^ k) |
          ℓ • ((g (k + 1) : W.Point)) = (g k : W.Point)} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter, IsCompatibleLevels]
  rw [hset]
  refine isClosed_iInter fun k => isClosed_eq ?_ ?_
  · exact (continuous_of_discreteTopology (f := fun P : W.Point => ℓ • P)).comp
      (continuous_subtype_val.comp (continuous_apply (k + 1)))
  · exact continuous_subtype_val.comp (continuous_apply k)

/-! ### The level-family map -/

/-- The **level family** of an element of the Tate module, packaged as an additive homomorphism
`T_ℓ E →+ ∏_k E[ℓ^k]`. This is the tautological map into the inverse system; the theorems below say
it is a closed topological embedding onto the compatible families. -/
@[simps]
def levelFamily : W.tateModule ℓ →+ ∀ k, W.torsion (ℓ ^ k) where
  toFun f k := proj k f
  map_zero' := rfl
  map_add' _ _ := rfl

theorem levelFamily_injective : Function.Injective (levelFamily W ℓ) := fun _ _ h =>
  tateModule.ext fun k => congrArg Subtype.val (congrFun h k)

/-- **The range of the level family is exactly the compatible families.** -/
theorem range_levelFamily :
    Set.range (levelFamily W ℓ) = {g : ∀ k, W.torsion (ℓ ^ k) | IsCompatibleLevels W ℓ g} := by
  ext g
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨f, rfl⟩ k
    exact f.2.2 k
  · intro hg
    exact ⟨⟨fun k => (g k : W.Point), ⟨fun k => (g k).2, hg⟩⟩, rfl⟩

/-- The inclusion of the product of the level groups into `ℕ → E(F)`, through which the level
family factors the coercion of `T_ℓ E`. -/
private def levelInclusion (g : ∀ k, W.torsion (ℓ ^ k)) : ℕ → W.Point := fun k => (g k : W.Point)

private theorem continuous_levelInclusion : Continuous (levelInclusion W ℓ) :=
  continuous_pi fun k => continuous_subtype_val.comp (continuous_apply k)

/-- The level family is continuous. -/
theorem continuous_levelFamily : Continuous (levelFamily W ℓ) :=
  continuous_pi fun k =>
    continuous_induced_rng.2 ((continuous_apply k).comp continuous_subtype_val)

/-- **The topology on `T_ℓ E` is the inverse-limit topology.** Formally: the level family is
inducing, i.e. the subspace topology `T_ℓ E` inherits from `ℕ → E(F)` coincides with the topology
pulled back from `∏_k E[ℓ^k]`.

The proof is the factorisation `levelInclusion ∘ levelFamily = Subtype.val`: the composite is
inducing because `T_ℓ E` carries the subspace topology by construction, so `IsInducing.of_comp`
gives it for the first factor. -/
theorem isInducing_levelFamily : Topology.IsInducing (levelFamily W ℓ) := by
  refine Topology.IsInducing.of_comp (continuous_levelFamily W ℓ)
    (continuous_levelInclusion W ℓ) ?_
  exact Topology.IsInducing.subtypeVal

theorem isEmbedding_levelFamily : Topology.IsEmbedding (levelFamily W ℓ) :=
  ⟨isInducing_levelFamily W ℓ, levelFamily_injective W ℓ⟩

/-- **`T_ℓ E ↪ ∏_k E[ℓ^k]` is a closed embedding**: `T_ℓ E` is homeomorphic, as a topological
group, onto a closed subgroup of the product of its levels. Everything below is a corollary. -/
theorem isClosedEmbedding_levelFamily : Topology.IsClosedEmbedding (levelFamily W ℓ) :=
  ⟨isEmbedding_levelFamily W ℓ, by
    rw [range_levelFamily]
    exact isClosed_setOf_isCompatibleLevels W ℓ⟩

/-! ### Compactness -/

/-- **`T_ℓ E` is compact whenever every level `E[ℓ^k]` is finite.** Tychonoff for the product of
finite discrete spaces, plus the closed embedding above. -/
theorem compactSpace (hfin : ∀ k, Finite (W.torsion (ℓ ^ k))) :
    CompactSpace (W.tateModule ℓ) := by
  haveI : ∀ k, CompactSpace (W.torsion (ℓ ^ k)) := fun k => by
    haveI := hfin k
    infer_instance
  exact (isClosedEmbedding_levelFamily W ℓ).compactSpace

/-- The set form of `compactSpace`: `T_ℓ E` is a compact subset of `ℕ → E(F)`. Note that the
ambient space is *not* compact — `E(F)` is infinite — so this is not inherited from it. -/
theorem isCompact_coe (hfin : ∀ k, Finite (W.torsion (ℓ ^ k))) :
    IsCompact ((W.tateModule ℓ : Set (ℕ → W.Point))) :=
  isCompact_iff_compactSpace.2 (compactSpace W ℓ hfin)

/-! ### The unconditional `ℓ = 2` layer -/

section Two

variable [IsAlgClosed F] [W.IsElliptic]

/-- **`T_2 E` is compact**, with no hypothesis beyond `(2 : F) ≠ 0`. The finiteness of every level
is `finite_torsion_two_pow`, which comes from `#E[2^k] = 4^k`; that count uses only the tangent-line
doubling identity, so this is independent of Ward's theorem, of the elliptic-net recurrence and of
the coordinate formula `x(nP) = Φₙ/ΨSqₙ`. -/
theorem compactSpace_two (h2 : (2 : F) ≠ 0) : CompactSpace (W.tateModule 2) :=
  compactSpace W 2 (finite_torsion_two_pow h2)

/-- **`T_2 E` is compact but not discrete.**

This is the statement that rules out the degenerate readings of everything above and of
`EllipticCurves.TateModule.Continuity`: a compact *discrete* space is finite, whereas `T_2 E` is
infinite (`infinite_tateModule_two`). So the profinite topology on `T_2 E` is genuinely a new
topology — neither indiscrete (it is Hausdorff) nor discrete — and the continuity statements proved
about it are not vacuous. It is also the precise reason a stabiliser in `T_2 E` can be closed
without being open. -/
theorem not_discreteTopology_tateModule_two (h2 : (2 : F) ≠ 0) :
    ¬ DiscreteTopology (W.tateModule 2) := by
  intro hd
  haveI := hd
  haveI := compactSpace_two W h2
  haveI := infinite_tateModule_two (W := W) h2
  haveI : Finite (W.tateModule 2) := finite_of_compact_of_discrete
  exact not_finite (W.tateModule 2)

/-- **`T_2 E` as an object of `ProfiniteAddGrp`**: a compact, totally disconnected topological
abelian group. `ProfiniteAddGrp.of` does not ask for `T2Space` — in a topological group, total
disconnectedness already forces it — so Hausdorffness is not being skipped here; it is
`tateModule.t2Space`. -/
def profiniteAddGrpTwo (h2 : (2 : F) ≠ 0) : ProfiniteAddGrp :=
  haveI := compactSpace_two W h2
  ProfiniteAddGrp.of (W.tateModule 2)

@[simp]
theorem coe_profiniteAddGrpTwo (h2 : (2 : F) ≠ 0) :
    (profiniteAddGrpTwo W h2 : Type _) = W.tateModule 2 :=
  rfl

end Two

/-! ### The level filtration is a filtration by open subgroups -/

/-- The kernel of the level-`k` projection is **open**: `E[ℓ^k]` is discrete and `proj k` is
continuous. Together with `iInf_ker_proj` this exhibits the level filtration as a neighbourhood
basis of `0` by open subgroups, which is what makes `T_ℓ E` the inverse limit of its quotients
`T_ℓ E ⧸ ker (proj k)`; that identification is not proved here. -/
theorem isOpen_ker_proj (k : ℕ) :
    IsOpen (((proj (W := W) (ℓ := ℓ) k).ker : AddSubgroup (W.tateModule ℓ)) :
      Set (W.tateModule ℓ)) := by
  have hset : (((proj (W := W) (ℓ := ℓ) k).ker : AddSubgroup (W.tateModule ℓ)) :
      Set (W.tateModule ℓ)) = (fun f => proj (W := W) (ℓ := ℓ) k f) ⁻¹' {0} := by
    ext f
    simp [AddMonoidHom.mem_ker]
  rw [hset]
  exact ((continuous_apply k).comp (continuous_levelFamily W ℓ)).isOpen_preimage _
    (isOpen_discrete _)

/-- The level filtration is **separated**: a compatible family vanishing at every level is `0`. -/
theorem iInf_ker_proj : (⨅ k : ℕ, (proj (W := W) (ℓ := ℓ) k).ker) = ⊥ := by
  refine le_antisymm (fun f hf => ?_) bot_le
  simp only [AddSubgroup.mem_iInf, AddMonoidHom.mem_ker] at hf
  exact AddSubgroup.mem_bot.2 (tateModule.ext fun k => congrArg Subtype.val (hf k))

end tateModule

end WeierstrassCurve.Affine
