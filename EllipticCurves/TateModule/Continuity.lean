/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.GaloisAction
import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Continuity of the `ℓ`-adic Galois representation

`EllipticCurves.TateModule.GaloisAction` builds
`ρ_ℓ = galoisRep ℓ : G →* (T_ℓE ≃ₗ[ℤ_[ℓ]] T_ℓE)` for `G = F ≃ₐ[S] F` purely as a homomorphism of
*abstract* groups, and says so. This file supplies the continuity that file does not.

⚠️ **This paragraph used to quote that file as saying** *"Continuity of `ρ_ℓ` for the profinite
topology on `G` and the `ℓ`-adic topology on `T_ℓ E` is not addressed here and is left to a
follow-up"*, **and that is no longer its text**: it now names `continuous_galoisRep` as the
discharge instead of promising a follow-up, and states the Krull/profinite gap that the retired
wording elided. ⚠️ **A quotation of another file's docstring goes stale exactly as the docstring
does**, and a sweep is the likeliest thing in the world to be editing both at once — re-check the
quotation in both files after touching either.

⚠️ It also used to add *"Every file built on top of it repeats the disclaimer"*, **and that was a
tally nobody had measured**. Measured: `EllipticCurves.TateModule.GaloisAction` has **44** modules
in its reverse import cone (excluding the root aggregator) and **10** of them carry a
continuity-is-not-asserted clause, so *every* was false when it was written and is false now. The
position the sentence was reaching for survives without a number: the disclaimer had already been
restated in more than one register — from a scope statement about a file's own contents to a claim
about the whole `ρ` front — and this file is what ends the need for either. ⚠️ **State the
position, not the tally.** The tally is the part that decays, so no count belongs on either side of
this sentence; the two above are pinned to this commit and are evidence for the retirement, not a
census to maintain.

## The topologies, and why nothing has to be constructed

`G` already carries the **Krull topology** as a Mathlib instance
(`Mathlib.FieldTheory.KrullTopology`), so there is nothing to set up on that side.

On the other side, `T_ℓE` is by construction an `AddSubgroup` of `ℕ → E(F)`. Give `E(F)` the
**discrete** topology; then `ℕ → E(F)` receives the product topology and `T_ℓE` the subspace
topology by instance search alone, and *that subspace topology is the `ℓ`-adic (inverse-limit)
topology*: a basic neighbourhood of `f` is the set of compatible families agreeing with `f` up to
level `k`, which is the coset `f + ℓ^k·T_ℓE` in disguise. So no inverse-limit topology has to be
built and no topology has to be transported along `ℤ_[ℓ]`.

The discrete topology on `E(F)` is supplied as a **scoped** instance, in the scope
`WeierstrassCurve.Affine.ProfiniteTopology`. It is scoped deliberately: `W.Point` carries no
topology anywhere in Mathlib or in this development, and a global instance would silently fix this
choice for every future file — including one that wants the archimedean or `v`-adic topology on
`E(K)` for a number field `K`, where the discrete topology is the wrong answer.

## The mathematical content

Everything reduces to one fact: **the stabiliser in `G` of a point of `E(F)` is open**
(`Point.isOpen_stabilizer`). A point is either `0`, whose stabiliser is everything, or `some x y h`
with `x y : F`, and `σ • some x y h = some (σ x) (σ y) _`, so its stabiliser is
`stabilizer G x ⊓ stabilizer G y`, open by Mathlib's `stabilizer_isOpen_of_isIntegral`.

That lemma is why `[Algebra.IsIntegral S F]` is assumed throughout. This is **not** a restriction in
practice: `F = AlgebraicClosure S` satisfies it, and that is the setting the rest of this front
works in — though over `S = ℚ` it takes a two-line repair rather than bare instance search, for a
reason that has nothing to do with elliptic curves; see the next section.
`Mathlib.RingTheory.Algebraic.Integral` is imported so that the instance
`Algebra.IsAlgebraic.isIntegral` is in scope at all, since neither `GaloisAction` nor
`KrullTopology` pulls it in.

The sharper, hypothesis-free statement — torsion points are algebraic over the field of
definition — needs the division polynomials and would gate this file on the front's main wall for
no gain.

Note that the stabiliser of an element of `T_ℓE` is in general only **closed**, not open
(`tateModule.isClosed_stabilizer`): it is the intersection over all levels `k` of the open
stabilisers of `f k`. That is exactly why `ρ_ℓ` is continuous without being locally constant, and
it is the sense in which `T_ℓE` is genuinely a topological rather than a discrete module.

## Using this file: the `ℚ`-algebra instance trap

Over `S = ℚ` the hypothesis `[Algebra.IsIntegral ℚ (AlgebraicClosure ℚ)]` is **not** found by
instance search in a file with a large import closure, even though it is found in a small one. The
cause is a genuine instance-priority artefact of Mathlib, not of this development: once
`DivisionRing.toRatAlgebra` is in scope — it arrives with the analysis imports that `ℤ_[ℓ]` pulls
in — it outranks `AlgebraicClosure.instAlgebra ℚ`, and `AlgebraicClosure.isAlgebraic` is registered
against the latter. `#synth Algebra ℚ (AlgebraicClosure ℚ)` reports which one you have.

The repair is two lines, and works because `ℚ`-algebra structures on a division ring are a
subsingleton:

```lean
have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
  rw [show (DivisionRing.toRatAlgebra : Algebra ℚ (AlgebraicClosure ℚ))
      = AlgebraicClosure.instAlgebra ℚ from Subsingleton.elim _ _]
  infer_instance
```

`Algebra.IsIntegral` then follows by `infer_instance`. No such problem arises over a base field that
is not `ℚ`: for instance `Algebra.IsIntegral (ZMod p) (AlgebraicClosure (ZMod p))` is found
directly.

## Main statements

* `WeierstrassCurve.Affine.Point.isOpen_stabilizer` : stabilisers of points are open in `G`.
* `WeierstrassCurve.Affine.Point.instContinuousSMul`,
  `WeierstrassCurve.Affine.tateModule.instContinuousSMul` : `G` acts continuously on `E(F)` and on
  `T_ℓE`.
* `WeierstrassCurve.Affine.tateModule.instContinuousSMulPadicInt` : `T_ℓE` is a topological
  `ℤ_[ℓ]`-module, so the `ℓ`-adic module structure and the topology are compatible.
* `WeierstrassCurve.Affine.continuous_galoisRep` : `ρ_ℓ` is continuous.
* `WeierstrassCurve.Affine.continuous_galoisRepMod` : the mod-`n` representation is continuous.
* `WeierstrassCurve.Affine.tateModule.isClosed_stabilizer` : stabilisers in `T_ℓE` are closed.
* `WeierstrassCurve.Affine.tateModule.isTopologicalAddGroup`,
  `WeierstrassCurve.Affine.tateModule.t2Space`,
  `WeierstrassCurve.Affine.tateModule.totallyDisconnectedSpace` : the structural facts, recorded.

## Scope

**No compactness**, and that scoping decision is unchanged. ⚠️ The *reason* this paragraph used to
give for it was two false clauses. The first, *"finiteness of `E[n]` is not available in this
development"*, is false for every `3`-smooth `n`: `finite_torsion_of_smooth`
(`EllipticCurves.Torsion.Multiplicative`), and its special cases `finite_torsion_two_pow` and
`finite_torsion_three_pow`. The second, *"(it needs the division-polynomial characterisation of
`E[n]`)"*, is a claim about a **route**, and the route actually taken denies it —
`card_torsion_le_sq_of_smooth`'s own docstring says the bound is obtained from `#E[2] ≤ 4` and
`#E[3] ≤ 9` *"purely by multiplicativity — no multiplication-by-`n` coordinate formula and no
elliptic-net recurrence are involved"*. Compactness is simply not this file's job: `T₂E` is compact,
unconditionally, and it is proved as `compactSpace_two` in
`EllipticCurves.TateModule.Profinite`, out of the generic `compactSpace` there, which takes
levelwise finiteness as a hypothesis exactly as this file's neighbours do. What is available here —
Hausdorff, totally disconnected, a topological group — follows from the construction and is
recorded below.

**The target topology in `continuous_galoisRep` is the topology of pointwise convergence** on
`T_ℓE → T_ℓE`, not the compact-open topology and not an operator topology. Continuity of the
`ℓ = 2` matrix form `galoisRepMatrixTwo b : G →* GL₂(ℤ_[2])` for the `2`-adic topology on `GL₂` is
not proved *here*, but it is proved, in `EllipticCurves.TateModule.MatrixContinuity`
(`continuous_galoisRepMatrixTwo`), out of the `ContinuousSMul` instance below. Earlier versions of
this docstring said it needed `b.repr` to be continuous, i.e. a basis compatible with the level
filtration; **that was wrong**, and no compatibility is needed: `b.equivFun.symm` is continuous for
*any* basis, its source `Fin 2 → ℤ_[2]` is compact and its target is Hausdorff, so `b.equivFun` is
continuous by `Continuous.homeoOfEquivCompactToT2`.

**Openness of the image** of `ρ_ℓ`, and any statement about `ker ρ_ℓ`, are out of scope.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open PadicInt

namespace WeierstrassCurve.Affine

/-! ### The discrete topology on points, as a scoped instance -/

namespace ProfiniteTopology

/-- The **discrete topology on the points of a Weierstrass curve**. Scoped: see the module
docstring — `W'.Point` has no topology by default, and fixing one globally would pre-empt the
archimedean and `v`-adic topologies that a future file may want on `E(K)`. -/
scoped instance instTopologicalSpacePoint {R : Type*} [CommRing R] (W' : Affine R) :
    TopologicalSpace W'.Point := ⊥

scoped instance instDiscreteTopologyPoint {R : Type*} [CommRing R] (W' : Affine R) :
    DiscreteTopology W'.Point :=
  ⟨rfl⟩

end ProfiniteTopology

open scoped ProfiniteTopology

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
variable [Algebra.IsIntegral S F]

/-! ### Stabilisers of points are open -/

omit [Algebra.IsIntegral S F] in
/-- The stabiliser of an affine point is cut out by the stabilisers of its two coordinates. -/
theorem Point.stabilizer_some_eq (x y : F) (h : (W'⁄F).Nonsingular x y) :
    (MulAction.stabilizer (F ≃ₐ[S] F) (Point.some x y h) : Set (F ≃ₐ[S] F))
      = (MulAction.stabilizer (F ≃ₐ[S] F) x : Set (F ≃ₐ[S] F)) ∩
          (MulAction.stabilizer (F ≃ₐ[S] F) y : Set (F ≃ₐ[S] F)) := by
  ext σ
  simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_inter_iff]
  constructor
  · intro hσ
    have h' : Point.some (σ x) (σ y)
        ((W'.baseChange_nonsingular (σ : F →ₐ[S] F).injective ..).mpr h) = Point.some x y h := hσ
    have h₂ : σ x = x ∧ σ y = y := by simpa only [Point.some.injEq] using h'
    exact h₂
  · rintro ⟨hx, hy⟩
    change Point.some (σ x) (σ y) _ = _
    simp only [Point.some.injEq]
    exact ⟨hx, hy⟩

/-- **The stabiliser of a point of `E(F)` is open in the Krull topology.** This is the one fact the
whole file rests on. For the point at infinity the stabiliser is all of `G`; for an affine point it
is the intersection of the stabilisers of its two coordinates, each open by Mathlib's
`stabilizer_isOpen_of_isIntegral`. -/
theorem Point.isOpen_stabilizer (P : (W'⁄F).Point) :
    IsOpen (MulAction.stabilizer (F ≃ₐ[S] F) P : Set (F ≃ₐ[S] F)) := by
  cases P with
  | zero =>
    convert isOpen_univ
    ext σ
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_univ, iff_true]
    exact smul_zero σ
  | some x y h =>
    rw [Point.stabilizer_some_eq]
    exact (stabilizer_isOpen_of_isIntegral x).inter (stabilizer_isOpen_of_isIntegral y)

/-- The automorphisms agreeing with `σ₀` at `P` form the left coset `σ₀ · Stab(P)`, hence an open
set. -/
theorem Point.isOpen_setOf_galois_smul_eq (P : (W'⁄F).Point) (σ₀ : F ≃ₐ[S] F) :
    IsOpen {σ : F ≃ₐ[S] F | σ • P = σ₀ • P} := by
  have hset : {σ : F ≃ₐ[S] F | σ • P = σ₀ • P}
      = (fun τ : F ≃ₐ[S] F => σ₀ * τ) '' (MulAction.stabilizer (F ≃ₐ[S] F) P : Set _) := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    constructor
    · intro hσ
      exact ⟨σ₀⁻¹ * σ, by rw [mul_smul, hσ, ← mul_smul, inv_mul_cancel, one_smul],
        by rw [← mul_assoc, mul_inv_cancel, one_mul]⟩
    · rintro ⟨τ, hτ, rfl⟩
      rw [mul_smul, hτ]
  rw [hset]
  exact (Homeomorph.mulLeft σ₀).isOpenMap _ (Point.isOpen_stabilizer P)

/-- The orbit map `σ ↦ σ • P` is continuous — equivalently, locally constant, since `E(F)` is
discrete. -/
theorem Point.continuous_galois_smul (P : (W'⁄F).Point) :
    Continuous fun σ : F ≃ₐ[S] F => σ • P := by
  refine continuous_iff_continuousAt.2 fun σ₀ => ?_
  rw [ContinuousAt, nhds_discrete ((W'⁄F).Point), Filter.tendsto_pure]
  exact (Point.isOpen_setOf_galois_smul_eq P σ₀).mem_nhds rfl

/-- **`G` acts continuously on `E(F)`.** Joint continuity, not just continuity of each orbit map:
near `(σ₀, P₀)` the action is constant on `(σ₀ · Stab P₀) × {P₀}`. -/
instance Point.instContinuousSMul : ContinuousSMul (F ≃ₐ[S] F) ((W'⁄F).Point) where
  continuous_smul := by
    refine continuous_iff_continuousAt.2 fun p => ?_
    obtain ⟨σ₀, P⟩ := p
    rw [ContinuousAt, nhds_discrete ((W'⁄F).Point), Filter.tendsto_pure, nhds_prod_eq]
    filter_upwards [Filter.prod_mem_prod
      ((Point.isOpen_setOf_galois_smul_eq P σ₀).mem_nhds rfl)
      (show ({P} : Set (W'⁄F).Point) ∈ nhds P by
        rw [nhds_discrete ((W'⁄F).Point)]; simp)] with q hq
    obtain ⟨hq₁, hq₂⟩ := hq
    rw [Set.mem_singleton_iff] at hq₂
    rw [show q.2 = P from hq₂]
    exact hq₁

/-! ### The Tate module -/

variable (ℓ : ℕ)

namespace tateModule

omit [Algebra.IsIntegral S F] in
/-- Reading off the level-`k` value is continuous: the topology on `T_ℓE` is by definition the one
induced from the product. -/
theorem continuous_coe_apply (k : ℕ) :
    Continuous fun f : (W'⁄F).tateModule ℓ => (f : ℕ → (W'⁄F).Point) k :=
  (continuous_apply k).comp continuous_subtype_val

omit [Algebra.IsIntegral S F] in
/-- The level projections `T_ℓE →+ E[ℓ^k]` are continuous. -/
theorem continuous_proj (k : ℕ) : Continuous (proj (W := W'⁄F) (ℓ := ℓ) k) := by
  rw [continuous_induced_rng]
  exact continuous_coe_apply ℓ k

/-- Each orbit map `σ ↦ σ • f` on the Tate module is continuous. -/
theorem continuous_galois_smul (f : (W'⁄F).tateModule ℓ) :
    Continuous fun σ : F ≃ₐ[S] F => σ • f := by
  rw [continuous_induced_rng]
  exact continuous_pi fun k => Point.continuous_galois_smul _

/-- **`G` acts continuously on `T_ℓE`.** Levelwise this is the joint continuity already proved for
`E(F)`. -/
instance instContinuousSMul : ContinuousSMul (F ≃ₐ[S] F) ((W'⁄F).tateModule ℓ) where
  continuous_smul := by
    rw [continuous_induced_rng]
    refine continuous_pi fun k => ?_
    exact continuous_smul.comp
      (continuous_fst.prodMk ((continuous_coe_apply ℓ k).comp continuous_snd))

omit [Algebra.IsIntegral S F] in
/-- The stabiliser of `f ∈ T_ℓE` is the intersection over all levels of the stabilisers of its
level values. -/
theorem stabilizer_eq_iInter (f : (W'⁄F).tateModule ℓ) :
    (MulAction.stabilizer (F ≃ₐ[S] F) f : Set (F ≃ₐ[S] F))
      = ⋂ k : ℕ, (MulAction.stabilizer (F ≃ₐ[S] F) ((f : ℕ → (W'⁄F).Point) k) :
          Set (F ≃ₐ[S] F)) := by
  ext σ
  simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_iInter]
  exact ⟨fun h k => congrFun (congrArg Subtype.val h) k, fun h => tateModule.ext fun k => h k⟩

/-- **Stabilisers in `T_ℓE` are closed, and in general not open.** They are intersections over all
levels of the open — hence also closed — stabilisers of the level values. This is precisely the
gap between `ρ_ℓ` being continuous and being locally constant, and the sense in which `T_ℓE` is not
a discrete module. -/
theorem isClosed_stabilizer (f : (W'⁄F).tateModule ℓ) :
    IsClosed (MulAction.stabilizer (F ≃ₐ[S] F) f : Set (F ≃ₐ[S] F)) := by
  rw [stabilizer_eq_iInter]
  exact isClosed_iInter fun k => OpenSubgroup.isClosed
    ⟨MulAction.stabilizer (F ≃ₐ[S] F) ((f : ℕ → (W'⁄F).Point) k),
      Point.isOpen_stabilizer ((f : ℕ → (W'⁄F).Point) k)⟩

end tateModule

/-! ### The `ℤ_[ℓ]`-module structure is topological -/

omit [Algebra.IsIntegral S F] in
/-- `toZModPow k` is locally constant: it is constant on the ball of radius `ℓ⁻ᵏ`. This is the only
input needed to see that the `ℓ`-adic scalar action on `T_ℓE` is continuous. -/
theorem _root_.PadicInt.toZModPow_eventuallyEq {p : ℕ} [Fact p.Prime] (k : ℕ) (a₀ : ℤ_[p]) :
    ∀ᶠ a in nhds a₀, toZModPow k a = toZModPow k a₀ := by
  have hp : (0 : ℝ) < p := mod_cast (Fact.out : p.Prime).pos
  rw [Metric.eventually_nhds_iff]
  refine ⟨(p : ℝ) ^ (-(k : ℤ)), zpow_pos hp _, fun {a} ha => ?_⟩
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, ker_toZModPow,
    ← norm_le_pow_iff_mem_span_pow]
  rw [dist_eq_norm] at ha
  exact ha.le

omit [Algebra.IsIntegral S F] in
/-- **`T_ℓE` is a topological `ℤ_[ℓ]`-module.** Without this, "the `ℓ`-adic topology on `T_ℓE`"
would be a name rather than a claim: it says the topology coming from the inverse limit is
compatible with the `ℤ_[ℓ]`-action, which acts on level `k` through `ZMod (ℓ^k)`. -/
instance tateModule.instContinuousSMulPadicInt [Fact ℓ.Prime] :
    ContinuousSMul ℤ_[ℓ] ((W'⁄F).tateModule ℓ) where
  continuous_smul := by
    rw [continuous_induced_rng]
    refine continuous_pi fun k => ?_
    refine continuous_iff_continuousAt.2 fun p => ?_
    obtain ⟨a₀, f₀⟩ := p
    rw [ContinuousAt, nhds_discrete ((W'⁄F).Point), Filter.tendsto_pure, nhds_prod_eq]
    have hf : IsOpen ((fun f : (W'⁄F).tateModule ℓ => (f : ℕ → (W'⁄F).Point) k) ⁻¹'
        {(f₀ : ℕ → (W'⁄F).Point) k}) :=
      (tateModule.continuous_coe_apply ℓ k).isOpen_preimage _ (isOpen_discrete _)
    filter_upwards [Filter.prod_mem_prod (PadicInt.toZModPow_eventuallyEq k a₀)
      (hf.mem_nhds rfl)] with q hq
    obtain ⟨hq₁, hq₂⟩ := hq
    change (toZModPow k q.1).val • (q.2 : ℕ → (W'⁄F).Point) k
      = (toZModPow k a₀).val • (f₀ : ℕ → (W'⁄F).Point) k
    rw [hq₁, show (q.2 : ℕ → (W'⁄F).Point) k = (f₀ : ℕ → (W'⁄F).Point) k from hq₂]

/-! ### Continuity of the representations -/

/-- **The `ℓ`-adic Galois representation is continuous**, for the Krull topology on `G` and the
topology of *pointwise convergence* on `T_ℓE → T_ℓE`.

This is the statement that upgrades `galoisRep` from a homomorphism of abstract groups to a
representation of the topological group `G`. It is not a statement about the compact-open topology
or about `GL₂(ℤ_[ℓ])` with its `ℓ`-adic topology; see the module docstring. -/
theorem continuous_galoisRep [Fact ℓ.Prime] :
    Continuous fun σ : F ≃ₐ[S] F =>
      (galoisRep ℓ σ : (W'⁄F).tateModule ℓ → (W'⁄F).tateModule ℓ) :=
  continuous_pi fun f => tateModule.continuous_galois_smul ℓ f

/-- The `G`-action on the `n`-torsion is continuous, jointly in `σ` and the point. -/
instance torsion.instContinuousSMul (n : ℕ) :
    ContinuousSMul (F ≃ₐ[S] F) ((W'⁄F).torsion n) where
  continuous_smul := by
    rw [continuous_induced_rng]
    exact continuous_smul.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/-- **The mod-`n` representation is continuous**, again for pointwise convergence on `E[n] → E[n]`.
`E[n]` is discrete, so this says each `σ ↦ σ • P` is locally constant; it does *not* say the
representation itself is locally constant, which would need `E[n]` to be finite. -/
theorem continuous_galoisRepMod (n : ℕ) :
    Continuous fun σ : F ≃ₐ[S] F =>
      (galoisRepMod n σ : (W'⁄F).torsion n → (W'⁄F).torsion n) := by
  refine continuous_pi fun P => ?_
  rw [continuous_induced_rng]
  exact Point.continuous_galois_smul _

/-! ### Structural facts

All of these hold by instance search from the construction; they are recorded under names so that a
reader can see what this topology does give. They are also what rules out the degenerate reading of
this file: continuity is vacuous into an indiscrete space, and `T2Space` together with
`Nontrivial (T_ℓE)` — available at `ℓ = 2` from `finrank_tateModule_two` — says the topology is not
indiscrete. Compactness is *not* among them; see the module docstring. -/

omit [Algebra.IsIntegral S F] in
/-- `T_ℓE` is a topological additive group. -/
theorem tateModule.isTopologicalAddGroup : IsTopologicalAddGroup ((W'⁄F).tateModule ℓ) :=
  inferInstance

omit [Algebra.IsIntegral S F] in
/-- `T_ℓE` is Hausdorff: two compatible families differing at some level are separated by that
level. -/
theorem tateModule.t2Space : T2Space ((W'⁄F).tateModule ℓ) :=
  inferInstance

omit [Algebra.IsIntegral S F] in
/-- `T_ℓE` is totally disconnected. Together with `IsTopologicalAddGroup` and `T2Space` this is
everything the profinite picture gives without finiteness of the `E[ℓ^k]`. -/
theorem tateModule.totallyDisconnectedSpace :
    TotallyDisconnectedSpace ((W'⁄F).tateModule ℓ) :=
  inferInstance

end WeierstrassCurve.Affine
